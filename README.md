# ITT

ITT supports the following modalities:
* **I** (irrelevance) -- erased at runtime, disregarded in conversion checks
* **E** (erased) -- erased at runtime, subject to conversion checks
* **L** (linear) -- present at runtime, linear
* **R** (unrestricted) -- present at runtime, unrestricted

ITT can infer all of them by interleaving type checking and constraint solving
using an external solver (Z3 via [SBV](http://hackage.haskell.org/package/sbv)).

ITT supports only variables, lambdas and applications so if you need global definitions,
you need to bring them into scope using lambdas.
Pattern matching is [work in progress](https://github.com/ziman/itt-idris/tree/adt).

The inference algorithm does not need any modality annotations to work.
However, any "primitives" you bring into scope with lambdas have no bodies
so the minimal consistent annotation is "everything is irrelevant".
You'll probably want to override this to give more meaning to your primitives.

You can look at [one of the example programs](https://github.com/ziman/itt-idris/blob/master/examples/simple.itt).
I'll commit the outputs once the calculus has stabilised a bit.

## Making it easier

Inference gets easier if you don't need to support all modalities.

* **I** requires interleaving conversion checking and constraint solving,
  iteratively, until you reach a fixed point where no new conversions arise.

* **L** requires counting constraints, which interferes with evar equalities.
  Namely, you can no longer express equality `p ~ q` as `(p -> q) /\ (q -> p)`.
  I use an external SMT solver to get it done.

If you leave out either of the two, you get an easier problem to solve
when inferring annotations.

## Usage

Build
```
$ idris -p contrib Main.idr -o itt
```

Run
```
$ ./itt examples/simple.itt
```

For editing, https://github.com/ziman/ttstar-vim might come handy.
