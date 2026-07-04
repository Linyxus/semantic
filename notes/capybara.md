# Capybara: the Surface Calculus for Separation and Ownership

Capybara is a surface calculus that gets compiled to CoreCapybara. It has simple syntax forms.

## Separation Checking

Separation checking in Capybara happens when type-checking term function applications. Let's consider a function `[c](x: T) ->Cf E`. Note that each term function explicitly has one capture parameter bound, thus the `[c]` part in the type. When this function is applied and we find an instance for `c`, let's say, `D`. Separation check should be performed between `D` and the _interfere set_ of the function type itself.

Interfere set is what the values of a type may use, either directly or indirectly. It is defined by the following rules:
```
interfere-set([c](x: S^C) ->Cf E) = Cf ∪ C ∪ interfere-set(E) - {c,x}
interfere-set([X] ->Cf E) = Cf ∪ interfere-set(E)
interfere-set([c] ->Cf E) = Cf ∪ interfere-set(E) - {c}
```

## Translation

Some examples for compiling a function type. Given the type:
```
[c](x: Ref^{a, c}) ->Cs () ->{a, x} Unit
```
It should be compiled into
```
[c] -> [cx <: {a, c}] -> (x: Ref^{cx}) -> {Cs, cx}[{c},{a}] () ->{a, cx} Unit
```

A type function:
```
[T] ->Cs E
```
It should be translated to
```
[T] -> [Ψ] E
```
Here, Ψ is computed by:
- getting all peaks of Cs in the source language, call it the peak set P
- for each peak c, get all access modes (mu1, mu2, mu3) in the P. Make it an item in SepCtx {mu1 c, mu2 c, mu3 c}

