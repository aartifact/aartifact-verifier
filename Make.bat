::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
::
:: aartifact
:: http://www.aartifact.org/src/
:: Copyright (C) 2008-2010
:: A. Lapets
::
:: This software is made available under the GNU GPLv3.
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
ghc -O2 --make -odir o -hidir hi Main -o aa.exe

::eof
