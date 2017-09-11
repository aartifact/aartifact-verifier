# aartifact-verifier

Lightweight formal verification system developed to support research on usability of automated proof verification tools.

## Background

This repository has been posted for archival purposes. The work that involved this verification system is described in a number of publications and reports (listed below):
* Andrei Lapets and Assaf Kfoury. [**A User-friendly Interface for a Lightweight Verification System**](http://www.cs.bu.edu/techreports/pdf/2010-011-aartifact-interface.pdf). *Electronic Notes in Theoretical Computer Science*, 285(C):29-41, 2012.
* Andrei Lapets. [**User-friendly Support for Common Concepts in a Lightweight Verifier**](http://www.cs.bu.edu/techreports/pdf/2010-010-aartifact-discussion.pdf). Proceedings of VERIFY-2010: The 6th International Verification Workshop. Edinburgh, UK. July 2010.
* Andrei Lapets, Prakash Lalwani, and Assaf Kfoury. [**Ontology Support for a Lightweight Formal Verification System**](http://www.cs.bu.edu/techreports/pdf/2010-012-aartifact-ontology.pdf). Technical Report BUCS-TR-2010-012, CS Dept., Boston University, May 2010.
* Andrei Lapets and David House. [**Efficient Support for Common Relations in Lightweight Formal Reasoning Systems**](http://www.cs.bu.edu/techreports/pdf/2009-033-efficient-verifier-relations.pdf). Technical Report BUCS-TR-2009-033, CS Dept., Boston University, November 2009.
* Andrei Lapets. [**Lightweight Formal Verification in Classroom Instruction of Reasoning about Functional Code**](http://www.cs.bu.edu/techreports/pdf/2009-032-classroom-verification-functional.pdf). Technical Report BUCS-TR-2009-032, CS Dept., Boston University, November 2009.

Subsequent publications describe later versions of the verification system inspired by the version in this repository:
* Andrei Lapets, Richard Skowyra, Azer Bestavros, and Assaf Kfoury. [**Towards Accessible Integration and Deployment of Formal Tools and Techniques**](http://cs-people.bu.edu/lapets/resource/topi2013-integdep.pdf). Proceedings of TOPI 2013: The 3rd Workshop on Developing Tools as Plug-ins. San Francisco, CA, USA. May 2013.
* Andrei Lapets. [**Accessible Integrated Formal Reasoning Environments in Classroom Instruction of Mathematics**](http://www.cs.bu.edu/techreports/pdf/2012-015-env-classroom-math.pdf). Proceedings of HCSS 2012: The High Confidence Software and Systems Conference. Annapolis, MD, USA. May 2012.

## Building and installing

Run the usual `cabal` command from the project's root directory:

    cabal install
    
## Running

A number of example proof scripts can be found in the `examples` directory. They can be processed as is done with the example below:

    aartifact -ascii examples/test.txt
    
The ASCII output should look as follows:

    \vbeg
    Introduce !!>$x$<!!.
    Assume !!>$x = 5$<!!.
    Assert !!>$x = 5$<!!.
    Assert <<<$x = 6$>>>.
    \vend
