Pardinus
=======

Pardinus is Kodkod's (slightly bulkier) Iberian cousin. 

<a href="https://travis-ci.org/haslab/Pardinus"><img align="right" alt="Build Status" src="https://travis-ci.org/haslab/Pardinus.svg?branch=master"/></a>

This repository includes the source code for the Pardinus solver, an extension to the [Kodkod](http://alloy.mit.edu/kodkod/index.html) solver for relational logic. It extends Kodkod with the following functionalities:
* Target-oriented and weighted-target oriented model finding
* Model finding over (past and future) LTL relational formulas
* Symbolic bound declarations
* Decomposed parallelized model finding
* Unbounded relational model finding

Pardinus is developed at the High-Assurance Software Laboratory ([HASLab](http://haslab.di.uminho.pt)), from INESC TEC and University of Minho, and is led by Alcino Cunha and Nuno Macedo. It is used as a back-end for [Electrum Analyzer](https://github.com/haslab/Electrum), which is itself an extension to the Alloy Analyzer.

Pardinus is open-source and available under the [MIT license](LICENSE), as is Kodkod. However, the implementation relies on third-party solvers ([SAT4J](http://www.sat4j.org), [MiniSat](http://minisat.se), [Glucose/Syrup](http://www.labri.fr/perso/lsimon/glucose/), [(P)Lingeling](http://fmv.jku.at/lingeling/), [Yices](http://yices.csl.sri.com), and [Electrod](https://github.com/grayswandyr/electrod/)), some of which are released under stricter licenses (see the various LICENSE files in the distribution for details).

## Building Pardinus

Pardinus inherits [Kodkod](https://github.com/emina/kodkod/blob/master/README.md#building-and-installing-kodkod)'s 
building and running instructions.

Kodkod uses the [Waf](https://github.com/waf-project/waf) build
system, which requires Python 2.5 or later. You will also need Java 8
and a C/C++ compiler, and your JAVA_HOME environment variable needs to
point to the JDK 8 home directory.

* Set the JAVA_HOME variable. For example, on OS X:

  ``$ export JAVA_HOME=`/usr/libexec/java_home` ``

* Clone the Pardinus repository:

  `$ git clone https://github.com/haslab/Pardinus.git`  
  `$ cd Pardinus`  

* Download Waf 1.8.12 and make it executable:

  `$ wget --no-check-certificate https://waf.io/waf-1.8.12`  
  `$ chmod u+x waf-1.8.12`   
  `$ alias waf=$PWD/waf-1.8.12`

* Build the native libraries, ``pardinus.jar``, and ``examples.jar`` and install them into the ``pardinus/lib`` directory:

  `$ waf configure --prefix=. --libdir=lib build install`  

## Collaborators
- Nuno Macedo, HASLab, INESC TEC & Universidade do Minho, Portugal, 2013 - present
- Alcino Cunha, HASLab, INESC TEC & Universidade do Minho, Portugal, 2013 - present
- Eduardo Pessoa, HASLab, INESC TEC & Universidade do Minho, Portugal, 2015 - 2016
- Tiago Guimarães, HASLab, INESC TEC & Universidade do Minho, Portugal, 2013 - 2014

## History
### Pardinus ([1.2.0](https://github.com/haslab/Pardinus/releases/tag/v1.2)) (August 2020)
- Major [changes](https://github.com/haslab/Pardinus/pull/40) to iteration operations

### Pardinus ([1.1.0](https://github.com/haslab/Pardinus/releases/tag/v1.1)) (April 2019)
- Major [changes](https://github.com/haslab/Pardinus/pull/29) to the solving engine

### Pardinus ([1.0.0](https://github.com/haslab/Pardinus/releases/tag/v1.0)) (January 2018)
<!--- FM,ABZ 18 submissions --->
- Support for unbounded model finding in SMV through [Electrod](https://github.com/grayswandyr/electrod/releases/tag/0.1)
- Support for [Electrum Analyzer 1.0](https://github.com/haslab/Electrum/releases/tag/v1.0)

### Pardinus ([0.3.1](https://github.com/haslab/Pardinus/releases/tag/v0.3.1)) (November 2016) 
<!--- TACAS 17 submission --->
- Support for symbolic bound declaration
- Described in the ATVA 17 [paper](https://doi.org/10.1007/978-3-319-68167-2_23)

### Pardinus ([0.3.0](https://github.com/haslab/Pardinus/releases/tag/v0.3.0)) (September 2016) 
<!--- TRUST Workshop 16 --->
- Initial support for (past and future) temporal model finding
- Support for [Electrum Analyzer 0.2](https://github.com/haslab/Electrum/releases/tag/v0.2)

### Pardinus ([0.2.0](https://github.com/haslab/Pardinus/releases/tag/v0.2.0)) (April 2016) 
<!--- ASE16 submission --->
- Initial support for decomposed model finding
- Support for Syrup (parallel Glucose)

### Pardinus (0.1.1) (October 2014) 
<!--- FASE15 submission -->
- Support for weighted target-oriented model finding
- Merged Alloy Analyzer's Kodkod 2.0 tweaks into Kodkod 2.1
- Supported scenario exploration operations from [extended Alloy Analyzer](toalloy.jar)
- Described in the FASE 15 [paper](http://dx.doi.org/10.1007/978-3-662-46675-9_20)

### Pardinus (0.1.0) (October 2013) 
<!--- FASE14 submission -->
- Initial support for target-oriented model finding
- Extended support to Max-SAT SAT4J and Yices
- Described in the FASE 14 [paper](http://dx.doi.org/10.1007/978-3-642-54804-8_2)

