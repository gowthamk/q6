TODO
=====

1. The current approach of handling pattern matches on symbolic lists
is not conducive to tail-recursive functions such as fold_left. ToDo: 
better approach.

2. Lists in the user program represent a special collections type that
supports only a subset of of list operations which do not lead to
exponential blowup of VCs. Usual list operations, such as cons and
nil, may lead to exponential blowup, hence come with no guarantees.
ToDo: clever encoding that supports lists and other recursive
structures.
