# Category Theory using SSReflect and Packed Classes

A category theory library intended for use in abstract/Grothendieck-style 
mathematics, e.g. modern algebraic geometry. This library uses packed classes to build a
hierarchy of categorical structures and the SSReflect proof language for proofs, 
in the MathComp style. We also use universe polymorphism to work around 
size issues, which can be a pain in category theory developed over traditional foundations 
of mathematics (e.g., ZFC).

This is also an experiment with doing "high-level"/abstract mathematics in MathComp, as MathComp has 
only been used to work with low-level objects like graphs and finite groups in the past.

Note however that this library is very classical, admitting proof irrelevance and functional 
extensionality as axioms. It is built with the intention to serve as basis of a development of
some basic algebraic geometric notions in MathComp.

## Usage
Generate the Makefile:

    coq_makefile -f _CoqProject -o Makefile

and then run `make`.

## Author
Xuanrui Qi ([xuanrui@nagoya-u.jp](mailto:xuanrui@nagoya-u.jp), [me@xuanruiqi.com](mailto:me@xuanruiqi.com)),
with the assistance of:

* [Reynald Affeldt](https://staff.aist.go.jp/reynald.affeldt/) (affeldt-aist)
* [Takafumi Saikawa](https://github.com/t6s)

## License
MIT License
