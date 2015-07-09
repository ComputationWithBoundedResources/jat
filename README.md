JAT (Jinja Analysation Tool)
============================

Provides a complexity reflecting transformatioin from Jinja bytecode to
(constraint) term rewrite system.

EXAMPLE USAGE
=============

Print help.
    $ jat -h

Analyse all methods in file `ListAppend.jbc`.
Results are stored as `ListAppend-Class-method.trs`:
    $ jat ListAppend.jbc

Analyse method `append` of class `List` in file `ListAppend.jbc`.
Result is printed to stdout:
    $ jat ListAppend.jbc List append 

Return graph representation as [dot](http://www.graphviz.org) file.
    $ jat -f DOT ListAppend.jbc

