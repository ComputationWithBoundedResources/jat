JAT (Jinja Analysation Tool)
============================

Provides a complexity preserving transformation from Jinja bytecode to term
rewrite system.  Further informations can be obtained
[here](http://cl-informatik.uibk.ac.at/cbr/jat).

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

