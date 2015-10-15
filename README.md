JAT (Jinja Analysation Tool)
============================

Provides a complexity preserving transformation from Jinja bytecode to
(constraint) term rewrite system.

EXAMPLE USAGE
=============

Print help.
```shell
jat -h
```

Analyse all methods in file `ListAppend.jbc`.
Results are stored as `ListAppend-Class-method.trs`:
```shell
jat ListAppend.jbc
```

Analyse method `append` of class `List` in file `ListAppend.jbc`.
Result is printed to stdout:
```shell
jat ListAppend.jbc List append 
```

Return graph representation as [dot](http://www.graphviz.org) file.
```shell
jat -f DOT ListAppend.jbc
```

