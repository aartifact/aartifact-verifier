::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
:: aartifact
:: http://www.aartifact.org/
::
:: Make.bat
::   Batch script for compiling with GHC under Windows
::   environments.

::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::

@IF EXIST o GOTO make
@MD o
@IF EXIST hi GOTO make
@MD hi
:make
ghc -O2 --make -fspec-constr-count=50 -odir o -hidir hi Main -o aa.exe

::eof