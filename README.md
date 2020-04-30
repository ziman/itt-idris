# ITT

ITT infers quantity/erasure annotations from pattern matching dependent programs.

ITT supports the following modalities:
* **I** (irrelevance) -- erased at runtime, disregarded in conversion checks
* **E** (erased) -- erased at runtime, subject to conversion checks
* **L** (linear) -- present at runtime, linear
* **R** (unrestricted) -- present at runtime, unrestricted

ITT can infer all of them by interleaving type checking and constraint solving
using an external solver.

The inference algorithm does not need any modality annotations to work.
However, any "primitives" you postulate have no bodies
so the minimal consistent annotation is "everything is irrelevant".
You'll probably want to override this to give more meaning to your primitives.

You can look at [one of the example programs](https://github.com/ziman/itt-idris/blob/master/examples/simple.itt)
and [its output](https://github.com/ziman/itt-idris/blob/master/examples/simple.out).
Here's a [vector length program](https://github.com/ziman/itt-idris/blob/master/examples/vect.itt)
and [its output](https://github.com/ziman/itt-idris/blob/master/examples/vect.out).

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
$ idris2 -p contrib Main.idr -o itt
```

Run
```
$ build/exec/itt examples/simple.itt
```
