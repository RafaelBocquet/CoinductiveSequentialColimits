This repository contains an Agda proof of results related to sequential colimits in HoTT

The base definitions of sequence and sequential colimits are in [NatColim.agda](NatColim.agda), where a coinduction principle for sequences, and alternative induction principles for sequential colimits are also proven.

Commutativity of sequential colimits and sigma types is proven in [CommSigma.agda](CommSigma.agda).
[CommSigma/Code.agda](CommSigma/Code.agda) defines the type that a colimit of sigma types is equivalent to. Maps in both directions are defined in [CommSigma/Maps.agda](CommSigma/Maps.agda), and they are proven to be quasi-inverses in [CommSigma/Paths.agda](CommSigma/Paths.agda).

Commutativity of sequential colimits and path types is proven in [CommPaths.agda](CommPaths.agda).
