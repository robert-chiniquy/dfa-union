#![cfg(test)]

use std::io::Write;

#[test]
fn test_graphviz() {
    setup();
    // let d1 = DfaState::from_str("*f*");
    // let d2 = DfaState::from_str("f*f*");
    // let g = graphviz("*f*", "f*f*");
    // let g = graphviz("*f", "f*q");
    let g = graphviz("*f", "f*f");
    // let g = graphviz("*", "*");

    let mut output = std::fs::File::create("./last.dot").unwrap();
    let _r = output.write_all(g.as_bytes());
}

#[test]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    // setup();
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
    let mut wins = 0;
    let mut losses = 0;
    for (a, b, o) in sources {
        let r = compare(a, b);
        if o == r {
            wins += 1;
        } else {
            losses += 1;
            println!("{a} {b} \t\t expected {o:?} got {r:?}");
        }
    }
    assert_eq!(losses, 0, "{wins} wins, {losses} losses");
    Ok(())
}

/// From http://cs.wellesley.edu/~cs235/fall09/lectures/14_DFA_operations/14_DFA_operations_revised.pdf
/// "To determine if DFA1 and DFA2 are equivalent, construct DFA1 x
/// DFA2 and examine all state pairs containing at least one accepting
/// state from DFA1 or DFA2:
/// • If in all such pairs, both components are accepting, DFA1 and
/// DFA2 are equivalent --- i.e., they accept the same language.
/// • If in all such pairs, the first component is accepting but in some
/// the second is not, the language of DFA1 is a superset of the
/// language of DFA2 and it is easy to find a string accepted by
/// DFA1 and not by DFA2
/// • If in all such pairs, the second component is accepting but in
/// some the first is not, the language of DFA1 is a subset of the
/// language of DFA2, and it is easy to find a string accepted by
/// DFA2 and not by DFA1
/// • If none of the above cases holds, the languages of DFA1 and
/// DFA2 are unrelated, and it is easy to find a string accepted by
/// one and not the other."
/// ^ The above does not cover intersection.
#[tracing::instrument(ret)]
fn compare(s1: &str, s2: &str) -> Outcome {
    let d1 = DfaNode::from_str(s1);
    let d2 = DfaNode::from_str(s2);
    let union = UnionNode::union(Some(&d1), Some(&d2));
    let ends = find_terminal_nodes(&union);
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
        // If we returned every terminal node, only the above cases would ever hit
        // however, if we exclude certain terminal nodes, we need to handle the below
        // cases as well.
        (true, false, false) => Outcome::Superset,
        (false, false, true) => Outcome::Subset,
        _ => {
            println!("{s1} {s2}: {ends:?}");
            unreachable!()
        }
    }
}

#[tracing::instrument(skip(u), ret)]
fn find_terminal_nodes(u: &UnionNode) -> Vec<TerminalState> {
    let mut ret = vec![];

    // if u.terminal != TerminalState::Not {
    //     ret.push(u.terminal);
    // }

    // for e in &u.edges {
    //     if let Edge::Forward(e) = e {
    //         ret.extend(find_terminal_nodes(&*e.next));
    //     }
    // }

    if u.edges.is_empty() {
        ret.push(u.terminal);
    } else {
        for e in &u.edges {
            if let Edge::Forward(e) = e {
                ret.extend(find_terminal_nodes(&*e.next));
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
    #[tracing::instrument(skip(self, l, r))]
    fn push_edge(&mut self, kind: Element, l: Option<&DfaNode>, r: Option<&DfaNode>) {
        let edge_node = UnionNode::union(l, r);
        let edge = Edge::Forward(ForwardEdge {
            kind,
            next: Box::new(edge_node),
        });
        self.edges.push(edge);
    }

    /// Always produces a new result node, consequently divering paths never rejoin
    /// and the resulting union DFA is not minimal and subtrees are duplicated
    #[tracing::instrument(ret, skip(l, r))]
    fn union(l: Option<&DfaNode>, r: Option<&DfaNode>) -> UnionNode {
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
                        ret.push_edge(kind.to_owned(), None, Some(&*next));
                    }
                }
            }
            (false, true) => {
                // recur on the left
                for l_e in &l_edges {
                    if let Edge::Forward(ForwardEdge { kind, next }) = l_e {
                        // outbound edge
                        ret.push_edge(kind.to_owned(), Some(&*next), None);
                    }
                }
            }
            (false, false) => {
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
                                        ret.push_edge(lfe.kind, Some(&*lfe.next), Some(&*rfe.next));
                                        if lfe.kind != Element::Star {
                                            if lfe.next.self_loop() {
                                                ret.push_edge(lfe.kind, l, Some(&*rfe.next));
                                            }
                                            if rfe.next.self_loop() {
                                                ret.push_edge(rfe.kind, Some(&*lfe.next), r);
                                            }
                                        }
                                    }
                                    ElementRelation::Disjoint => {
                                        // two edges to two discrete nodes
                                        ret.push_edge(lfe.kind, Some(&*lfe.next), None);
                                        ret.push_edge(rfe.kind, None, Some(&*rfe.next));
                                    }
                                    ElementRelation::Subset => {
                                        // two edges,
                                        // one to the union of the two with the kind of the subset,
                                        // one superset edge to the right
                                        // (the one that the subset does not match)
                                        ret.push_edge(lfe.kind, Some(&*lfe.next), Some(&*rfe.next));
                                        // a star can't fail to match, anywhere there is a self-loop,
                                        // it can continue forever. So do not recur over the possibility
                                        // that it stops.
                                        // if it is a self-loop on the left, do not traverse the right without the left
                                        if rfe.next.self_loop() {
                                            ret.push_edge(lfe.kind, Some(&*lfe.next), r);
                                            if !l.as_ref().unwrap().self_loop() {
                                                ret.push_edge(rfe.kind, None, Some(&*rfe.next));
                                            }
                                        } else {
                                            ret.push_edge(lfe.kind, Some(&*lfe.next), None);
                                        }
                                    }
                                    ElementRelation::Superset => {
                                        // two edges,
                                        // one to the union of the two with the kind of the subset,
                                        // one superset edge to the left
                                        ret.push_edge(rfe.kind, Some(&*lfe.next), Some(&rfe.next));
                                        if lfe.next.self_loop() {
                                            // there is a superset case where the star state does
                                            // not advance.
                                            ret.push_edge(rfe.kind, l, Some(&*rfe.next));
                                            if !r.as_ref().unwrap().self_loop() {
                                                ret.push_edge(lfe.kind, Some(&*lfe.next), None);
                                            }
                                        } else {
                                            ret.push_edge(rfe.kind, None, Some(&*rfe.next));
                                        }
                                    }
                                }
                            }
                            (Edge::Forward(lfe), Edge::Loop) => {
                                // one edge to the union of the current R node and lfe.next
                                ret.push_edge(lfe.kind, Some(&*lfe.next), r);
                            }
                            (Edge::Loop, Edge::Forward(rfe)) => {
                                // one edge to the union of the current L node and rfe.next
                                ret.push_edge(rfe.kind, l, Some(&*rfe.next));
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
    // Matt is ashamed of this.
    #[tracing::instrument(skip(d1, d2), ret)]
    fn new(d1: &Option<&DfaNode>, d2: &Option<&DfaNode>) -> Self {
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
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct DfaNode {
    id: usize,
    /// terminal if edges is empty
    edges: Vec<Edge>,
}

impl DfaNode {
    /// every node either only proceeds, or proceeds and also self-loops
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
enum Edge<S = DfaNode> {
    Forward(ForwardEdge<S>),
    Loop,
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct ForwardEdge<S = DfaNode> {
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

#[test]
fn test_a() {
    let d1 = DfaNode::from_str("a");
    assert_eq!(d1.id, 2);
    let d2 = DfaNode::from_str("a");
    let union = UnionNode::union(Some(&d1), Some(&d2));
    let ends = find_terminal_nodes(&union);
    assert_eq!(ends, vec![TerminalState::LR]);
}

impl DfaNode {
    #[tracing::instrument(ret)]
    fn from_str(s: &str) -> DfaNode {
        let mut id = 0;
        let mut id = || -> usize {
            id += 1;
            id
        };
        let terminal = DfaNode {
            id: id(),
            edges: vec![],
        };
        if s.is_empty() {
            terminal
        } else {
            let mut cursor: Option<DfaNode> = Some(terminal);
            // construct the DFA backwards so the next value is always available
            // and complete, so it can be moved.
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
                let state = DfaNode { id: id(), edges };
                cursor.replace(state);
            }
            // cursor now contains the entry state node
            cursor.unwrap()
        }
    }
}

fn setup() {
    let subscriber = tracing_subscriber::fmt();
    let subscriber = subscriber.with_span_events(tracing_subscriber::fmt::format::FmtSpan::ACTIVE);
    let subscriber = subscriber.finish();
    let _ = tracing::subscriber::set_global_default(subscriber);
}

fn graphviz(s1: &str, s2: &str) -> String {
    let d1 = DfaNode::from_str(s1);
    let d2: DfaNode = DfaNode::from_str(s2);
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
