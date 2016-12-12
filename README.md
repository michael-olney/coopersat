# coopersat: Cooper's Algorithm for QFLIA

This is a simple solver for quantifier-free linear integer arithmetic. It uses
[Cooper's algorithm][1] and is written in Haskell. To build and install, use
cabal in the root of the repository working directory:

    $ cabal build
    $ cabal install

The test suite runs randomly-generated instances against
[Iavor S. Diatchki's solver][2] (imported through cabal) which uses a different
algorithm:

    $ cabal test

The tests may take a few minutes to run if the instances generated are
difficult.

[1]: https://www.cs.cmu.edu/~emc/spring06/home1_files/Cooper.pdf
[2]: https://hackage.haskell.org/package/presburger
