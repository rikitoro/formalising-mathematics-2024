/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default
import Combinatorics.SimpleGraph.Basic


-- definition of graph
-- definition of graph
/-

# Graph theory

A year ago Lean's graph theory was a bit patchy, but now I think
it's robust enough to be taken seriously as a topic for a final project.

So, how do graphs work in Lean? Actually it took a long time
to come up with a definition people were happy with. One issue
is that different people mean different things by "graph". In this
section we're going to stick to "simple graphs", which means
that you have a type of vertices `V`, and edges go between two
distinct vertices in `V`. The rules for a simple graph:

1) Edges are undirected (so they don't have a source and a target, they
just have two ends, which are vertices)
2) You can't have more than one edge between two distinct vertices.
3) You can't have an edge going from a vertex to itself.

Because of rule 2, you can represent an edge as a yes/no question:
"is there an edge between `v` and `w` or not?". In other words
you can represent edges as a function `adj: V → V → Prop`, and you
don't need a separate set or type `E` for edges. `adj` is short
for "adjacent", so `adj v w` means "there's an edge between `v` and `w`,
i.e. "`v` is adjacent to `w`".

Rule 1 means that `adj` is symmetric (if `v` is adjacent to `w` then
`w` is adjacent to `v`), and rule 3 means that it is irreflexive,
i.e. `∀ v, ¬ adj v v`.

Here's how to say "let `G` be a (simple) graph with vertex set `V`"

-/
/-

# Graph theory

A year ago Lean's graph theory was a bit patchy, but now I think
it's robust enough to be taken seriously as a topic for a final project.

So, how do graphs work in Lean? Actually it took a long time
to come up with a definition people were happy with. One issue
is that different people mean different things by "graph". In this
section we're going to stick to "simple graphs", which means
that you have a type of vertices `V`, and edges go between two
distinct vertices in `V`. The rules for a simple graph:

1) Edges are undirected (so they don't have a source and a target, they
just have two ends, which are vertices)
2) You can't have more than one edge between two distinct vertices.
3) You can't have an edge going from a vertex to itself.

Because of rule 2, you can represent an edge as a yes/no question:
"is there an edge between `v` and `w` or not?". In other words
you can represent edges as a function `adj: V → V → Prop`, and you
don't need a separate set or type `E` for edges. `adj` is short
for "adjacent", so `adj v w` means "there's an edge between `v` and `w`,
i.e. "`v` is adjacent to `w`".

Rule 1 means that `adj` is symmetric (if `v` is adjacent to `w` then
`w` is adjacent to `v`), and rule 3 means that it is irreflexive,
i.e. `∀ v, ¬ adj v v`.

Here's how to say "let `G` be a (simple) graph with vertex set `V`"

-/
variable (V : Type) (G : SimpleGraph V)

-- Here's how to say two edges are adjacent
example (v w : V) : Prop :=
  G.Adj v w

-- If v is adjacent to w then w is adjacent to v
example (v w : V) : G.Adj v w → G.Adj w v :=
  G.adj_symm

-- v isn't adjacent to itself
example (v : V) : ¬G.Adj v v :=
  G.irrefl

/-

Longish interlude: here's how to make a square graph. It's quite laborious. 
Lean is better at proving theorems than making explicit examples!

v1 -- v2
|     |
|     |
v3 -- v4
-/
section SquareGraph

-- the vertex set of the square graph; we make it a type with four terms
inductive SqV : Type
  | v1 : SqV
  | v2 : SqV
  | v3 : SqV
  | v4 : SqV

open SqV

-- so I can write `v1` not `sqV.v1`
-- here's one boring way of making the edges -- an inductive proposition
inductive SqE : SqV → SqV → Prop
  | e12 : SqE v1 v2
  | e21 : SqE v2 v1
  | e24 : SqE v2 v4
  | e42 : SqE v4 v2
  | e34 : SqE v3 v4
  | e43 : SqE v4 v3
  | e13 : SqE v1 v3
  | e31 : SqE v3 v1

-- Now let's make the graph
def sqG : SimpleGraph SqV where
  Adj := SqE
  symm :=
    by
    -- do all the cases for the two vertices and the edge
    rintro (_ | _ | _ | _) (_ | _ | _ | _) (_ | _ | _ | _ | _ | _ | _ | _)
    -- now 8 goals; find the right constructor for sqE in all cases
    repeat' constructor
  loopless := by rintro (_ | _ | _ | _) (_ | _ | _ | _ | _ | _ | _ | _)

end SquareGraph

-- Here's how to make a triangle graph; it's rather easier
-- Here `fin 3` is the "canonical" type with 3 terms; to give a term of type `fin 3`
-- is to give a pair consisting of a natural `n` and a proof that `n < 3`.
-- Here the `complete_graph` function is doing all the work for you.
example : SimpleGraph (Fin 3) :=
  completeGraph (Fin 3)

-- The collection of all simple graphs on a fixed vertex set `V` form a Boolean algebra
-- (whatever that is)
example : BooleanAlgebra (SimpleGraph V) := by infer_instance

-- and in particular they form a lattice, so you can do stuff like this:
example : SimpleGraph V :=
  ⊥

-- empty graph
example : SimpleGraph V :=
  ⊤

-- complete graph
example (G H : SimpleGraph V) : SimpleGraph V :=
  G ⊔ H

-- union of vertices
-- etc etc, and you can even do this
example (G : SimpleGraph V) : SimpleGraph V :=
  Gᶜ

-- complement, i.e. an edge exists in `Gᶜ` between
-- distinct vertices `v` and `w` iff it doesn't
-- exist in `G`
-- The *support* of a graph is the vertices that have an edge coming from them.
example (v : V) : v ∈ G.support ↔ ∃ w, G.Adj v w := by rfl

-- true by definition
-- The `neighbor_set` of a vertex is all the vertices connected to it by an edge.
example (v : V) : Set V :=
  G.neighborSet v

example (v w : V) : w ∈ G.neighborSet v ↔ G.Adj v w :=
  Iff.rfl

-- true by defn
-- The type `sym2 V` is the type of unordered pairs of elements of `V`, i.e. `V × V`
-- modulo the equivalence relation generated by `(v,w)~(w,v)`.
-- So you can regard the edges as a subset of `sym2 V`, and that's `G.edge_set`
example : Set (Sym2 V) :=
  G.edgeSetEmbedding

-- You can use `v ∈ e` notation if `e : sym2 v`
-- For example, `G.incidence_set v` is the set of edges coming out of `v`,
-- regarded as elements of `sym2 V`
example (v : V) : G.incidenceSet v = {e ∈ G.edgeSetEmbedding | v ∈ e} :=
  rfl

-- You can delete a set of edges from `G` using `G.delete_edges`
example (E : Set (Sym2 V)) : SimpleGraph V :=
  G.deleteEdges E

-- if E contains edges not in G then this doesn't matter, they're just ignored.
-- You can push a graph forward along an injection
example (W : Type) (f : V ↪ W) : SimpleGraph W :=
  G.map f

-- and pull it back along an arbitrary map
example (U : Type) (g : U → V) : SimpleGraph U :=
  G.comap g

-- The degree of a vertex is the size of its neighbor_set.
-- Better assume some finiteness conditions to make this work.
variable [G.LocallyFinite]

-- now we have `finset` versions of some `set` things. For example
example (v : V) : G.degree v = Finset.card (G.neighborFinset v) :=
  rfl

-- If `H` is another graph on a vertex set `W`
variable (W : Type) (H : SimpleGraph W)

-- then we can consider types of various maps between graphs
example : Type :=
  G →g H

-- maps f:V → W such that v₁~v₂ -> f(v₁)~f(v₂)
example : Type :=
  G ↪g H

-- injections f : V → W such that v₁~v₂ ↔ f(v₁)~f(v₂)
example : Type :=
  G ≃g H

-- isomorphisms of graphs
