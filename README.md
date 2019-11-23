# Adam Chlipala, Certified Programming with Dependent Types 和訳プロジェクト

[![CircleCI](https://circleci.com/gh/cpdt-japanese/cpdt-japanese/tree/master.svg?style=svg)](https://circleci.com/gh/cpdt-japanese/cpdt-japanese/tree/master)


## How to build

### install package for Debian systems

```
$ sudo apt-get install build-essential coq texlive texlive-lang-japanese lmodern texlive-latex-extra
```

### build .glob and documents

```
$ make coq   ## make -j N coq  # may be faster
$ make doc
```
