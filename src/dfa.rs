#![cfg(test)]

use std::{collections::btree_set::Union, io::Write};

#[test]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    setup();
    let sources = vec![
        //  for later
        // ("*?", "*?", Outcome::Equal),
        // ("***", "*?*",  Outcome::Equal),
        ("*f", "f*f", Outcome::Superset),
        ("f*f", "*f", Outcome::Subset),
        ("*f*", "*f*", Outcome::Equal),
        ("*f*", "f*f*", Outcome::Superset),
        ("f*f*", "*f*", Outcome::Subset),
        ("asdf*f*", "*&f*", Outcome::Subset),
        ("asdf*f**", "*f*", Outcome::Subset),
        ("*b", "*", Outcome::Subset),
        ("*", "*", Outcome::Equal),
        ("f*", "*", Outcome::Subset),
        ("a*", "a", Outcome::Disjoint),
        ("a", "a*", Outcome::Disjoint),
        ("**", "*?*", Outcome::Superset),
        ("**", "*f", Outcome::Superset), // nb
        ("*?*", "***", Outcome::Subset),
        ("aab", "a?", Outcome::Disjoint),
        ("?", "*", Outcome::Subset),
        ("??", "*", Outcome::Subset),
        ("*", "", Outcome::Disjoint),
        ("*", "f*", Outcome::Superset),
        ("**", "*f*", Outcome::Superset),
        ("a", "*", Outcome::Subset),
        ("*", "a", Outcome::Superset),
        ("a*", "*a", Outcome::Intersection),
        ("a", "a", Outcome::Equal),
        ("aa", "a", Outcome::Disjoint),
        ("a", "aa", Outcome::Disjoint),
        ("a*b*z", "a*c*z", Outcome::Intersection),
        ("a", "a*b", Outcome::Disjoint),
    ];
    for (a, b, o) in sources {
        let r = compare(a, b);
        assert_eq!(o, r, "{a} {b} {r:?}");
    }
    Ok(())
}

#[tracing::instrument(ret)]
fn compare(s1: &str, s2: &str) -> Outcome {
    let d1 = DfaState::from_str(s1);
    let d2 = DfaState::from_str(s2);
    let union = UnionNode::union(Some(&d1), Some(&d2));
    let ends = visit(&union);
    match (
        ends.contains(&TerminalState::L),
        ends.contains(&TerminalState::LR),
        ends.contains(&TerminalState::R),
    ) {
        (true, true, true) => Outcome::Intersection,
        (true, true, false) => Outcome::Superset,
        (true, false, true) => Outcome::Disjoint,
        (false, true, true) => Outcome::Subset,
        (false, true, false) => Outcome::Equal,
        _ => unreachable!(),
    }
}

fn visit(u: &UnionNode) -> Vec<TerminalState> {
    let mut ret = vec![];
    if u.edges.is_empty() {
        ret.push(u.terminal);
    } else {
        for e in &u.edges {
            if let Edge::Forward(e) = e {
                ret.extend(visit(&*e.next));
            }
        }
    }
    ret
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
enum Outcome {
    Equal,
    Subset,   // L < R
    Superset, // L > R
    Intersection,
    Disjoint,
}

#[derive(Debug)]
struct UnionNode {
    terminal: TerminalState,
    l_id: Option<usize>,
    r_id: Option<usize>,
    /// this is owned rather than a reference, consequently
    /// diverging paths never rejoin and subtrees are duplicated
    edges: Vec<Edge<UnionNode>>,
}

impl UnionNode {
    /// Always produces a new result node, consequently divering paths never rejoin
    /// and the resulting union DFA is not minimal and subtrees are duplicated
    #[tracing::instrument(ret)]
    fn union(l: Option<&DfaState>, r: Option<&DfaState>) -> UnionNode {
        // takes 1 or 2 dfa nodes, and returns a union node (recur)
        // for each edge in L and R, determine the combination of dfa nodes to attach to it
        // de-duping edges
        // then for each of these edges, recur to construct the target node, then
        // connect the edge to the target node, and return the source node
        let mut ret = UnionNode {
            terminal: TerminalState::new(&l, &r),
            l_id: l.as_ref().map(|o| o.id),
            r_id: r.as_ref().map(|o| o.id),
            edges: vec![],
        };
        let l_edges: Vec<_> = l.as_ref().map(|o| o.edges.clone()).unwrap_or_default();
        let r_edges: Vec<_> = r.as_ref().map(|o| o.edges.clone()).unwrap_or_default();

        match (l_edges.is_empty(), r_edges.is_empty()) {
            (true, true) => (), // terminal for both
            (true, false) => {
                // recur on the right
                for r_e in &r_edges {
                    if let Edge::Forward(ForwardEdge { kind, next }) = r_e {
                        // outbound edge
                        let target = UnionNode::union(None, Some(&*next));
                        let fe: ForwardEdge<UnionNode> = ForwardEdge {
                            kind: kind.to_owned(),
                            next: Box::new(target),
                        };
                        ret.edges.push(Edge::Forward(fe));
                    }
                }
            }
            (false, true) => {
                // recur on the left
                for l_e in &l_edges {
                    if let Edge::Forward(ForwardEdge { kind, next }) = l_e {
                        // outbound edge
                        let target = UnionNode::union(Some(&*next), None);
                        let fe: ForwardEdge<UnionNode> = ForwardEdge {
                            kind: kind.to_owned(),
                            next: Box::new(target),
                        };
                        ret.edges.push(Edge::Forward(fe));
                    }
                }
            }
            (false, false) => {
                // complicated
                // the self loop only matters here for product against the
                // potential other side forward edge, ignore in the other cases
                // composite edge type is always the including / most inclusive element
                for l_e in &l_edges {
                    for r_e in &r_edges {
                        match (l_e, r_e) {
                            (Edge::Forward(lfe), Edge::Forward(rfe)) => {
                                match lfe.kind.relate(&rfe.kind) {
                                    ElementRelation::Identity => {
                                        // one edge to a union node
                                        // self loops on the union node don't matter for dfa comparison
                                        let union =
                                            UnionNode::union(Some(&*lfe.next), Some(&*rfe.next));
                                        let edge = Edge::Forward(ForwardEdge {
                                            kind: lfe.kind,
                                            next: Box::new(union),
                                        });
                                        ret.edges.push(edge);
                                        if lfe.next.self_loop() {
                                            let keep_l = UnionNode::union(l, Some(&*rfe.next));
                                            let edge = Edge::Forward(ForwardEdge {
                                                kind: lfe.kind,
                                                next: Box::new(keep_l),
                                            });
                                            ret.edges.push(edge);
                                        }
                                        if rfe.next.self_loop() {
                                            let keep_r = UnionNode::union(Some(&*lfe.next), r);
                                            let edge = Edge::Forward(ForwardEdge {
                                                kind: rfe.kind,
                                                next: Box::new(keep_r),
                                            });
                                            ret.edges.push(edge);
                                        }
                                    }
                                    ElementRelation::Disjoint => {
                                        // two edges to two discrete nodes
                                        let l_u = UnionNode::union(Some(&*lfe.next), None);
                                        let l_edge = Edge::Forward(ForwardEdge {
                                            kind: lfe.kind,
                                            next: Box::new(l_u),
                                        });
                                        ret.edges.push(l_edge);
                                        let r_u = UnionNode::union(None, Some(&*rfe.next));
                                        let r_edge = Edge::Forward(ForwardEdge {
                                            kind: rfe.kind,
                                            next: Box::new(r_u),
                                        });
                                        ret.edges.push(r_edge);
                                    }
                                    ElementRelation::Subset => {
                                        // two edges,
                                        // one to the union of the two with the kind of the subset,
                                        // one superset edge to the right
                                        // (the one that the subset does not match)
                                        let union =
                                            UnionNode::union(Some(&*lfe.next), Some(&*rfe.next));
                                        ret.edges.push(Edge::Forward(ForwardEdge {
                                            kind: lfe.kind,
                                            next: Box::new(union),
                                        }));
                                        // a star can't fail to match, anywhere there is a self-loop,
                                        // it can continue forever. So do not recur over the possibility
                                        // that it stops.
                                        // if it is a self-loop on the left, do not traverse the right without the left
                                        if rfe.next.self_loop() {
                                            let l_sup = UnionNode::union(Some(&*lfe.next), r);
                                            ret.edges.push(Edge::Forward(ForwardEdge {
                                                kind: lfe.kind,
                                                next: Box::new(l_sup),
                                            }));
                                            if !l.as_ref().unwrap().self_loop() {
                                                let only_star =
                                                    UnionNode::union(None, Some(&*rfe.next));
                                                ret.edges.push(Edge::Forward(ForwardEdge {
                                                    kind: rfe.kind,
                                                    next: Box::new(only_star),
                                                }));
                                            }
                                        } else {
                                            let l_sup = UnionNode::union(Some(&*lfe.next), None);
                                            ret.edges.push(Edge::Forward(ForwardEdge {
                                                kind: lfe.kind,
                                                next: Box::new(l_sup),
                                            }));
                                        }
                                    }
                                    ElementRelation::Superset => {
                                        // two edges,
                                        // one to the union of the two with the kind of the subset,
                                        // one superset edge to the left
                                        let union =
                                            UnionNode::union(Some(&*lfe.next), Some(&rfe.next));
                                        ret.edges.push(Edge::Forward(ForwardEdge {
                                            kind: rfe.kind,
                                            next: Box::new(union),
                                        }));
                                        if lfe.next.self_loop() {
                                            // there is a superset case where the star state does
                                            // not advance.
                                            let r_sup = UnionNode::union(l, Some(&*rfe.next));
                                            ret.edges.push(Edge::Forward(ForwardEdge {
                                                kind: rfe.kind,
                                                next: Box::new(r_sup),
                                            }));
                                            if !r.as_ref().unwrap().self_loop() {
                                                let only_star =
                                                    UnionNode::union(Some(&*lfe.next), None);
                                                ret.edges.push(Edge::Forward(ForwardEdge {
                                                    kind: lfe.kind,
                                                    next: Box::new(only_star),
                                                }));
                                            }
                                        } else {
                                            // println!("OOO {} {}", lfe.next.id, rfe.next.id);
                                            let r_sup = UnionNode::union(None, Some(&*rfe.next));
                                            ret.edges.push(Edge::Forward(ForwardEdge {
                                                kind: rfe.kind,
                                                next: Box::new(r_sup),
                                            }));
                                        }
                                    }
                                }
                            }
                            (Edge::Forward(lfe), Edge::Loop) => {
                                // one edge to the union of the current R node and lfe.next
                                let partial = UnionNode::union(Some(&*lfe.next), r);
                                ret.edges.push(Edge::Forward(ForwardEdge {
                                    kind: lfe.kind,
                                    next: Box::new(partial),
                                }));
                            }
                            (Edge::Loop, Edge::Forward(rfe)) => {
                                // one edge to the union of the current L node and rfe.next
                                let partial = UnionNode::union(l, Some(&*rfe.next));
                                ret.edges.push(Edge::Forward(ForwardEdge {
                                    kind: rfe.kind,
                                    next: Box::new(partial),
                                }));
                            }
                            // unimportant here, leave unimpl'd
                            (Edge::Loop, Edge::Loop) => (),
                        }
                    }
                }
            }
        }

        ret
    }

    fn graphviz(&self) -> String {
        let nodename = format!(
            r#"node_l{}_r{}"#,
            self.l_id.unwrap_or(0),
            self.r_id.unwrap_or(0)
        );
        let node_label = format!(
            "{} {} {:?}",
            self.l_id.unwrap_or(0),
            self.r_id.unwrap_or(0),
            self.terminal
        );
        let edges: String = self
            .edges
            .iter()
            .flat_map(|e| match e {
                Edge::Forward(fe) => {
                    let label = format!("{:?}", fe.kind);
                    let target = format!(
                        r#"node_l{}_r{}"#,
                        fe.next.l_id.unwrap_or(0),
                        fe.next.r_id.unwrap_or(0)
                    );
                    let rest = fe.next.graphviz();
                    Some(format!(
                        r#"{} -> {} [label="{}"];
    {}"#,
                        nodename, target, label, rest
                    ))
                }
                Edge::Loop => None,
            })
            .collect();
        format!(
            r#"{}[label="{}"];
    {}
"#,
            nodename, node_label, edges
        )
    }
}

#[derive(PartialEq, Eq, Copy, Clone)]
enum TerminalState {
    L,
    R,
    LR,
    Not,
}

impl std::fmt::Debug for TerminalState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::L => write!(f, "L"),
            Self::R => write!(f, "R"),
            Self::LR => write!(f, "LR"),
            Self::Not => write!(f, ""),
        }
    }
}

impl TerminalState {
    /// Matt is ashamed of this.
    fn new(d1: &Option<&DfaState>, d2: &Option<&DfaState>) -> Self {
        match (
            d1.as_ref().map(|d| d.id).unwrap_or(0),
            d2.as_ref().map(|d| d.id).unwrap_or(0),
        ) {
            (0, 0) => unreachable!(),
            (1, 1) => TerminalState::LR,
            (1, _) => TerminalState::L,
            (_, 1) => TerminalState::R,
            (_, _) => TerminalState::Not,
        }
        /*
        match (
            d1.as_ref().map(|o| o.edges.is_empty()).unwrap_or(false),
            d2.as_ref().map(|o| o.edges.is_empty()).unwrap_or(false),
        ) {
            (true, true) => TerminalState::LR,
            (true, false) => TerminalState::L,
            (false, true) => TerminalState::R,
            (false, false) => TerminalState::Not,
        }
        */
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct DfaState {
    id: usize,
    /// terminal if edges is empty
    edges: Vec<Edge>,
}

impl DfaState {
    fn self_loop(&self) -> bool {
        for e in &self.edges {
            match e {
                Edge::Forward(_) => (),
                Edge::Loop => return true,
            }
        }
        false
    }

    fn graphviz(&self, l: &str) -> String {
        let nodename = format!(r#"{l}_{}"#, self.id,);
        let node_label = format!("{}", self.id);
        let edges: String = self
            .edges
            .iter()
            .flat_map(|e| match e {
                Edge::Forward(fe) => {
                    let label = format!("{:?}", fe.kind);
                    let target = format!(r#"{l}_{}"#, fe.next.id,);
                    let rest = fe.next.graphviz(l);
                    Some(format!(
                        r#"{} -> {} [label="{}"];
    {}"#,
                        nodename, target, label, rest
                    ))
                }
                Edge::Loop => None,
            })
            .collect();
        format!(
            r#"{}[label="{}"];
    {}
"#,
            nodename, node_label, edges
        )
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum Edge<S = DfaState> {
    Forward(ForwardEdge<S>),
    Loop,
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct ForwardEdge<S = DfaState> {
    kind: Element,
    next: Box<S>,
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Element {
    Token(char),
    Star,
    Question,
}

impl std::fmt::Debug for Element {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Token(arg0) => write!(f, "{}", arg0),
            Self::Star => write!(f, "*"),
            Self::Question => write!(f, "?"),
        }
    }
}

enum ElementRelation {
    Identity,
    Disjoint,
    Subset,   // L < R
    Superset, // L > R
}

impl Element {
    // treat identity and inclusion as the same relation, as the same work results?
    // or have a return type enum indicating directionality
    //TODO ?? or return a reference to the most inclusive element if either includes the other?
    fn relate(&self, other: &Element) -> ElementRelation {
        match (self, other) {
            // each char value is a proceed edge type
            (Element::Token(c1), Element::Token(c2)) => {
                if c1 == c2 {
                    ElementRelation::Identity
                } else {
                    ElementRelation::Disjoint
                }
            }
            (Element::Token(_), Element::Star) => ElementRelation::Subset,
            (Element::Token(_), Element::Question) => ElementRelation::Subset,
            (Element::Star, Element::Token(_)) => ElementRelation::Superset,
            (Element::Star, Element::Star) => ElementRelation::Identity,
            (Element::Star, Element::Question) => ElementRelation::Superset,
            (Element::Question, Element::Token(_)) => ElementRelation::Superset,
            (Element::Question, Element::Star) => ElementRelation::Subset,
            (Element::Question, Element::Question) => ElementRelation::Identity,
        }
    }
}

impl From<char> for Element {
    fn from(c: char) -> Self {
        match c {
            '*' => Element::Star,
            '?' => Element::Question,
            c => Element::Token(c),
        }
    }
}

impl DfaState {
    fn from_str(s: &str) -> DfaState {
        let mut id = 0;
        let mut id = || -> usize {
            id += 1;
            id
        };
        let terminal = DfaState {
            id: id(),
            edges: vec![],
        };
        if s.is_empty() {
            terminal
        } else {
            let mut cursor: Option<DfaState> = Some(terminal);
            // construct the DFA backwards so the next value is always available
            // and complete, so it can be moved
            // end on the entry node and return it
            for c in s.chars().rev() {
                if c == '*' {
                    // if a star, set a self-loop flag on the target state
                    // this self-loop is used in the union function
                    if let Some(cursor) = cursor.as_mut() {
                        cursor.edges.push(Edge::Loop)
                    }
                }
                let edges = vec![Edge::Forward(ForwardEdge {
                    kind: c.into(),
                    next: Box::new(cursor.take().unwrap()),
                })];
                let state = DfaState { id: id(), edges };
                cursor.replace(state);
            }
            // cursor now contains the entry state node
            cursor.unwrap()
        }
    }
}

#[tracing::instrument(ret)]
fn compose(a: Outcome, b: Outcome) -> Outcome {
    match (a, b) {
        (x, y) if x == y => x,

        (x, Outcome::Disjoint) => x,
        (Outcome::Disjoint, x) => x,

        (Outcome::Equal, x) => x,
        (x, Outcome::Equal) => x,

        (Outcome::Subset, Outcome::Superset) => Outcome::Intersection,
        (Outcome::Superset, Outcome::Subset) => Outcome::Intersection,

        (Outcome::Intersection, _) => Outcome::Intersection,
        (_, Outcome::Intersection) => Outcome::Intersection,
        _ => unreachable!(),
    }
}

fn setup() {
    let subscriber = tracing_subscriber::fmt();
    let subscriber = subscriber.with_span_events(tracing_subscriber::fmt::format::FmtSpan::ACTIVE);
    let subscriber = subscriber.finish();
    let _ = tracing::subscriber::set_global_default(subscriber);
}

#[test]
fn test_graphviz() {
    setup();
    // let d1 = DfaState::from_str("*f*");
    // let d2 = DfaState::from_str("f*f*");
    // let g = graphviz("*f*", "f*f*");
    let g = graphviz("*f", "f*f");
    let mut output = std::fs::File::create("./last.dot").unwrap();
    let _r = output.write_all(g.as_bytes());
}

fn graphviz(s1: &str, s2: &str) -> String {
    let d1 = DfaState::from_str(s1);
    let d2: DfaState = DfaState::from_str(s2);
    let union = UnionNode::union(Some(&d1), Some(&d2));
    let label = format!(r#"{s1}\n{s2}"#);

    format!(
        r#"
strict digraph G {{
    rankdir = LR;
    remincross = true;
    label = "{label}";

    {}
    subgraph clusterDfa {{
        rankdir = LR;
        subgraph cluster1 {{
            label = "L {}";
            {}
        }}

        subgraph cluster2 {{
            label = "R {}";
            {}
        }}
    }}
}}
"#,
        union.graphviz(),
        s1,
        d1.graphviz("d1"),
        s2,
        d2.graphviz("d2")
    )
}
