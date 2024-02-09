# PyLambda-OG
Python Wrapper for Walter Fontana's LambdaC Reducer

# About
This Python 3 package can be used to interface with the `LambdaC` executable from Walter Fontana and Leo Buss. The original software is hosted here: https://sites.santafe.edu/~walter/AlChemy/software.html 

This package only wraps the lambda reducer `LambdaC` and not the entire AlChemy base model. 

Some modifications have been made to the original C code in order to expose the `reduce_lambda()` function. The original, unmodified C code (and makefile) are available through the link above or in the branch `LambdaC` of this repository.