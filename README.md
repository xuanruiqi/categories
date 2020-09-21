# MathComp Category Theory

A MathComp category theory library intended for use in category-heavy/Grothendieck-style 
mathematics, e.g. modern algebraic geometry. This library uses packed classes to build a
hierarchy of categorical structures. We also use universe polymorphism to work around 
size issues, which can be a pain in category theory developed over traditional foundations 
of mathematics (e.g., ZFC).

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
