# regex2smtlib

regex2smtlib is a tool for generating constraints in [SMT-LIB
format](http://smtlib.cs.uiowa.edu/language.shtml) from Perl compatible
regular expressions strings. At the moment, the input formats for
[Z3](https://github.com/z3prover/z3),
[Z3-str2](https://sites.google.com/site/z3strsolver/) and
[CVC4](http://cvc4.cs.stanford.edu/web/) are supported.

# Status

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)][licence]
[![Language](http://img.shields.io/badge/language-java-brightgreen.svg)][language]
[![Linux Build Status](https://img.shields.io/travis/hycos/regex2smtlib/master.svg?label=Linux%20build)][travis]
[![Test Coverage](https://codecov.io/gh/hycos/regex2smtlib/branch/master/graph/badge.svg)][coverage]

[licence]: https://opensource.org/licenses/mit
[language]: https://www.java.com
[travis]: https://travis-ci.org/hycos/regex2smtlib
[coverage]: https://codecov.io/gh/hycos/regex2smtlib

# TOC

[Integration](#integration)

[API Usage](#api-usage)

[Licence](#licence)


# Integration

regex2smtlib is available on maven central and can be integrated by
using the following dependency in the `pom.xml` file. 

```xml
<dependency>
    <groupId>com.github.hycos</groupId>
    <artifactId>regex2smtlib</artifactId>
    <version>1.0</version>
</dependency>
```

Please note that for running `mvn test`, [Docker](https://www.docker.com/) has
to be present on your system.

# API Usage

The API of regex2smtlib is very easy to use. The following example
generates a constraint in SMT-LIB format for matching `v1`
against the regular expression pattern `abc*`

```java
// format can be z3, cvc4 or z3str2
String constraint =
Translator.INSTANCE.translateToConstraint("z3","abc*","v1");
```

The call to `translateToConstraint` generates a constraint that
can be directly plugged into the respective constraint solver (in this case
`z3`).

```bash
(declare-fun v1 () String)
(assert (str.in.re v1  (re.++  (str.to.re "a") (re.++  (str.to.re "b") (re.*  (str.to.re "c") )))))
(check-sat)
(get-model)
```

The `Translator` class has two other member functions which may be useful:

```java
// generate SMT-LIB regex string only
String regexsmt = Translator.INSTANCE.translate("z3", "abc*");
// generate clause
String clause = Translator.INSTANCE.translateToClause("z3", "abc*", "v1");
```

The first line below corresponds to the value assigned to `regexsmt` after the
call to `translate()` in the snippet above, whereas the second line corresponds
to the value assigned to the variable `clause` after the call to
`translateToConjunct()`.

```bash
(re.++  (str.to.re "a") (re.++  (str.to.re "b") (re.*  (str.to.re "c") )))
(assert (str.in.re v1  (re.++  (str.to.re "a") (re.++  (str.to.re "b") (re.*  (str.to.re "c") )))))
```

In case you want to get more examples, please have a look at the JUnit test
cases.

# Licence

The MIT License (MIT)

Copyright (c) 2017 Julian Thome <julian.thome.de@gmail.com>

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
of the Software, and to permit persons to whom the Software is furnished to do
so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
