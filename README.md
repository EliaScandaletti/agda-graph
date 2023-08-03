## Module structure
The module has multiple submodules:
- `Core`
- `Common`
- `Directed`
- `Undirected`

The first two modules are flexible and can be used for any kind of graph, while the others define specific types of graph.
The remaining modules define different types of graph by using the generic definitions given in `Core` and by defining a predicate representing the edge set.
The `Common` module uses this predicate to specialize to different types of graphs.

#### `Core`
- `Core` contains the definition of `Graph`;
- `Core.Definitions` defines the predicate for the vertex set of a graph and a subset relation between them;
- `Core.Decidability` assuming that the vertex labels have a decidable equality, proves that the predicates given in `Core.Definitions` are decidable;
- `Core.Recursion` proves that recursion on the definition size of the graph -i.e. the number of Graph constructors used- is well-founded.

#### `Common`
This module requires to know a predicate defining the edge set of a graph.
- `Common.Definitions` defines a subset relation on edge sets, a subset relation on graphs and an equivalence on graphs;
- `Common.Properties` proves that the previously defined equivalence is really an equivalence and some properties of the subset relation between graphs;
- `Common.Decidability` assuming that an edge belonging to a graph is decidable and that the labels have a decidable equality, proves that the predicates given in `Common.Definitions` are decidable.

#### `Directed`
This module defines directed graphs.
- `Directed.Core` defines a predicate representing the edge set of a directed graph;
- `Directed.Properties` proves some properties of directed graphs that depend on the definition of the edge set;
- `Directed.Decidability` assuming that the vertex labels have a decidable equality, proves that an edge belonging to a directed graph is decidable, therefore proving the properties in `Common.Decidability`.

#### `Undirected`
This module defines undirected graphs.
- `Undirected.Core` defines a predicate representing the edge set of a undirected graph;
- `Undirected.Properties` proves some properties of undirected graphs that depend on the definition of the edge set;
- `Undirected.Decidability` assuming that the vertex labels have a decidable equality, proves that an edge belonging to a undirected graph is decidable, therefore proving the properties in `Common.Decidability`.