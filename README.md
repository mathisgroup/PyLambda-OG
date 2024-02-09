# PyLambda-OG
Python Wrapper for Walter Fontana's LambdaC Reducer

# About
This Python 3 package can be used to interface with the `LambdaC` executable from Walter Fontana and Leo Buss. The original software is hosted here: https://sites.santafe.edu/~walter/AlChemy/software.html 

This package only wraps the lambda reducer `LambdaC` and not the entire AlChemy base model. 

Some modifications have been made to the original C code in order to expose the `reduce_lambda()` function. The original, unmodified C code (and makefile) are available through the link above or in the branch `LambdaC` of this repository.

# Requirements and Install
This software has only been tested on Ubuntu 22.04 with Python 3.8, and gcc 11.1.0. It will not work on Windows systems (however it will work with WSL). It might work with a Mac, but good luck. 

I have not taken the time to make this work with a single `pip` install command. You'll need to run the following:

```
$ cd LambdaC/
$ make
$ cd ..
$ pip install -e .
```

The `-e` on the pip install is required because I haven't bothered to copy the shared library to the install location. The `-e` flag gets around this by installing the library where you cloned it.

You can test the install using `pytest`

```
$ pytest tests/
```

# Examples

## Simple

## Slightly less simple

## Failure Modes