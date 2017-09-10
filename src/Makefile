################################################################
##
## aartifact
## http://www.aartifact.org/
##
## Makefile
##   Basic makefile for compiling with GHC under Linux
##   environments.

################################################################
##

CC = ghc
CCFLAGS = -O2 --make -fspec-constr-count=50 -odir o -hidir hi
SRCS = *.hs
TARGET = Main
EXECUTABLE = aa

all: ${SRCS}
	if [ ! -d "./o" ] ; then mkdir o; fi
	if [ ! -d "hi" ] ; then mkdir hi; fi
	${CC} ${CCFLAGS} ${TARGET} -o $(EXECUTABLE)

clean:
	rm -rf o
	rm -rf hi

#eof