## Module structure
The `Graph` module has multiple submodules:
- `Common`
- `Core`
- `Directed`
- `Undirected`

Furthermore, there is the `Algo` module that proves some properties useful in the other modules.

The `Common` module defines gives definitions and proves property of graphs of any type.
In any submodule the graph type is taken as a module parameter, along some other required definitions and properties related to the given graph type.
This allows for maximum flexibility  of the module.

The `Core` module defines the `Graph` type and some of its properties. The definitions and properties regards the vertices of the graph.

The `Directed` and `Undirected` modules provide additional definitions regarding the edges of a `Core.Graph`.

#### `Common`
This module requires to know a predicate defining the edge set of a graph.
Each submodule may require to know additional properties.
- `Common.Definitions` defines a subset relation on edge sets, a subset relation on graphs and an equivalence on graphs;
- `Common.Properties` proves that the previously defined equivalence is really an equivalence and some properties of the subset relation between graphs;
- `Common.Decidability` assuming that an edge belonging to a graph is decidable and that the vertices have a decidable equality, proves that the predicates given in `Common.Definitions` are decidable;
- `Common.Weighted` defines weighted graphs;
- `Core.Algo.Definitions` defines `edges` and `adjacency-list` functions that given a graph return respectively the list of edges and the adjacency list of the graph;
- `Core.Algo.Properties` proves that `edges` and `adjacency-list` are correct.

#### `Core`
- `Core` contains the definition of `Graph`;
- `Core.Definitions` defines the predicate for the vertex set of a graph and a subset relation between them;
- `Core.Decidability` assuming that the vertices have a decidable equality, proves that the predicates given in `Core.Definitions` are decidable;
- `Core.Recursion` proves that recursion on the definition size of the graph -i.e. the number of Graph constructors used- is well-founded;
- `Core.Algo.Definitions` defines a `vertices` function that given a `Graph` returns the list of vertices;
- `Core.Algo.Properties` proves that `vertices` is correct.

#### `Directed`
This module defines directed graphs.
- `Directed` defines a predicate representing the edge set of a directed graph;
- `Directed.Properties` proves some properties of directed graphs that depend on the definition of the edge set;
- `Directed.Decidability` assuming that the vertex labels have a decidable equality, proves that an edge belonging to a directed graph is decidable, therefore proving the properties in `Common.Decidability`.

#### `Undirected`
This module defines undirected graphs.
- `Undirected` defines a predicate representing the edge set of a undirected graph;
- `Undirected.Properties` proves some properties of undirected graphs that depend on the definition of the edge set;
- `Undirected.Decidability` assuming that the vertex labels have a decidable equality, proves that an edge belonging to a undirected graph is decidable, therefore proving the properties in `Common.Decidability`.