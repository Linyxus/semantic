# From `Heap` to `Memory`

This is an ongoing work in the Semantic.CC module.

A `Memory` is a `Heap` that is well-formed. It is a structure with a heap and the proof that this heap is well-formed.

We want to have a transition from using `Heap`s to using `Memory`.

Where we used `Hpost`, we should use `Mpost` instead. For `Denot` and `PreDenot` types in the Denotation module, we should also use `Memory`.

