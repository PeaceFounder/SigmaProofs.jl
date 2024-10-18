# SigmaProofs.jl

[![codecov](https://codecov.io/gh/PeaceFounder/SigmaProofs.jl/graph/badge.svg?token=6LUFS7ZZPE)](https://codecov.io/gh/PeaceFounder/SigmaProofs.jl)

SigmaProofs is an ultimate swiss knife for implementing cryptogrpahic protocols that uses group based zero knowledge proofs often having commitment, challenge and reply structure for the proofs. This package includes a Verificatum compatable parser which is easuy to use for writting challenges and doing serialization/deserialization of a whole simulator which can often be a rather daunting task. Easy to use ElGamal implementation is also made necessary for reencryption mixnets as further used by ShuffleProofs.jl.

The provided proofs are made verifier agnostic making it easy to explore the specification space for writing challenges for the proofs and implement different generator basis algorithms. Every proof is treated as simulator that consists of three parts:

- `Proposition`: the statement that is being proved with a followiong proof type
- `Proof`: a proof that supports the statement
- `Verifier`: a verifier that participates in proof generation and can attest validity of the proof

The `Verifier` is often made noninteractive via FiatShamir transformation nevertheless if one wishes interacive proofs are also supported. This is possible to do via the same codebas as Julia does not colour functions with `@async` as many other programing languages do (although you would probably not need this). 

The methods that are uniformly implemnted are `prove(::Proposition, secrets..., ::Verifier)::Proof`, `challenge(::Verifier, ::Proposition, args...)`, `verify(::Proposition, ::Proof, ::Verifier)::Bool` and `proof_type(::Type{<:Proposition})::Type{<:Proof}`. To make the proofs convinient to use most of the proposition types expose construction methods that has semantics `construct(args..., secrets..., ::Verifier)::Simulator` like for instance `exponentiate(g, sk, verifier)`. The simulator has fields `proposition`, `proof`, `verifier` and can be convininiently verified via `verify(::Simulator)::Bool` method. In addition there is `generator_basis(::Verifier, ::Type{<:Group}, N)::Vector{G}` that produces independent generator basis vector particulalry useful for generalized pedersen commitments.

The `SigmaProofs` implements a *Verificatum* inspired verifier that provides the same `Verifier` semantics, uses the same generator basis algorithm as in Verificatum specification. The challenges to the proofs with the verifier are constructed using binary tree parser as given in the specification implemnted in `Parsers` module. However, it is important to not that only `ShuffleProofs` is implemented to be compatable with the *Verificatum* psecification as other proof types are not considered there. This package can be looked as a one possible way for verifier extension to other proof types. 

## LogProofs

- `LogProofs` The basis of the zero knowledge, for proving statements `PK{(x): y <- g^x}` which is known in the literature as *SchnorrProof* used for proving the knowledge of an exponent linking two public group elements `(g, y)`. On it's basis via adding a `suffix` message to the challenge a cryptographic signature is made known as *SchnorrSignature*. The other type of the proof is `PK{(x): A_i y_i <- g_i^x }` which proves that a lsit of pairs `(g_i, y_i)` has the same exponent known as *ChaumPedersenProof*. 

```julia
using CryptoGroups
using SigmaProofs.LogProofs: exponentiate, verify
using SigmaProofs.Verificatum

g = @ECGRoup{P_192}()
verifier = ProtocolSpec(; g)

sk = 42
pk = g^sk

g_vec = [g, g^2, g^5]
simulator = exponentiate(g_vec, sk, verifier)

verify(simulator) # true

simulator.proposition.y == [pk, pk^2, pk^5] # true
```

## ElGamal and DecryptionProofs

 ElGamal cypherrtext is encoded in `ElGamalRow` type which can be initialized with `(a, b)` either being elements of a group or an a tuple of elements representing generalized ElGamal cypheretxt that can extend the amount of information that can be encoded. When initialized with a single group element or a tupel it is presumed to be a message. The type suppports `width` method telling how wide the encoded cyphertext is.

ElGamalRow elements can conviniently be reencrypted with encryptor initialized with `Enc` type and then also decrypted with `Dec`. Convineitly the encryptor can also be used to initialize the cyphertexts.

```julia
using CryptoGroups

g = @ECGRoup{P_192}()

sk = 42
pk = g^sk

enc = Enc(pk, g)
dec = Dec(sk)

plaintexts = (g^2, g^5)
r = (8, 10)

ciphertext = enc(plaintexts, r) 
ciphertext == ElGamalRow(g .^ r, pk .^r .* m) # true

dec(ciphertext) == plaintexts # 
width(ciphertext) == 2 

# Arithmetic operations `*`, `^` and `/` are also supported

dec(ciphertext * cyphertext) == plaintexts .* plaintexts
dec(ciphertext ^ 7) == plaintexts .^ 7
dec(ciphertext / enc(ciphertext, r)) == (one(g), one(g))
```
The latter division can be used as plaintext equivalence test for the package. The arithmetic operations are convinient to make some zero knowledge proof implementations more coincise.

`DecryptionProofs` takes *CahumPedersenProofs* and uses them to construct `ElGamalRow` cypheretext vector and can produce coresponding zero knowledge proofs of correct decryption:

```julia
using CryptoGroups
using SigmaProofs.ElGamal: Enc, ElGamalRow
using SigmaProofs.DecryptionProofs: exponentiate, verify

g = @ECGroup{P_192}()
verifier = ProtocolSpec(; g)


sk = 123
pk = g^sk

encryptor = Enc(pk, g)

plaintexts = [g^4, g^2, g^3]
cyphertexts = encryptor(plaintexts, rand(2:order(g)-1, length(plaintexts))) .|> ElGamalRow

simulator = decrypt(g, cyphertexts, sk, verifier)

verify(simulator) # true
simultor.proposition.plaintexts == plaintexts
```

## RangeProofs

Range proofs allow one tow prove to the verifier that an integer within a certain cyphertext or a commit is within a given range without revealing it in the first place. The most simple method is `bitenc` that can produce proof that given elgamal cyphertex is either `(g^r, pk^r * 𝐺) OR (g^r, pk^r / 𝐺)` without revealing `r`. 
```
simulator = bitenc(g, pk, true, verifier)
@test verify(simulator)
```
the proposition `ElGamalBitRange` contains fields `x` and `y` that are elgamal encryptions. The proof is taken directly from a paper:

- [1]: Ronald Cramer, Rosario Gennaro, and Berry Schoenmakers. 1997. A secure and optimally efficient multi-authority election scheme. In Proceedings of the 16th annual international conference on Theory and application of cryptographic techniques (EUROCRYPT'97). Springer-Verlag, Berlin, Heidelberg, 103–118. https://link.springer.com/chapter/10.1007/3-540-69053-0_9

To commit arbitrary values n-arry decomposition is used. It is possible to reduce used group elements making the proof for commits only. For that we have a `bitcommit(g::G, h::G, value::Bool, verifier::Verifier)::Simulator` function which is analougous to `bitenc` except now `h` must be indeoendent from `g` and produces pedersen commitment in the result.

The `bitcommit` function is generalized with n-ary decomposition into `rangecommit(range::Union{Int, UnitRange}, g::G, h::G, value::Int, ::Verifier)`. When the range is integer then the range is assumed to be `0 <= value < 2^n`. Arbitray ranges can be useful for identity based signatures. The general idea is that client generates and identity provider signs your commitment `C = h^β * g^v`. The value can encode birth date or latitude/longtitude which can allow to prove to a service provider that your age is over 18 or that you live in a particular contry via issuing a requested range proof. Such setup prevents the identity provider to learn when or what you have accessed.

Another application of range commitments is that they can be used in a sealed bid auctions. An intersting variant is a Vickrey auction where the highest bidder wins but pasy the second-highest bid price. In such scheme the bidder signs a commitment and sends that to the dealer along with oppening. The dealer publishes the commitment on the buletin baord while keeps signature and oppening a secret. When all `bids <- h^β * g^v` are collected the dealer can anounce and prove the winner via running 
```
simulator = vickrey_auction(bids, g, h, 𝛃, verifier)` 
verify(simulator) # true

(; winner, value_win) = simulator.proposition
```
where the `winner` is the index in the list of bids and `value_win` is the winning value. The contract obligation then can be enforced by the dealer anouncing the signature while leaving other bidders' identitites and their bidded values secret. For full example see `examples/auctions.jl`.

The last piece of puzzle is range proof use in homomorphic tallying methods using in some evoting system designs. Here the vote is ElGamal encrypted and then homomoprhically talllied with only resulting tally being decrypted in trheshold decryption ceremony without revelaing individual votes. For this process to work, however, there is a need to ensure that voters had cast their votes honestly within allowed range. For simple `yes/no` referenda one would use `bitenc` wheras for multiple options one can make range encryption proofsexposed with `rangeenc(range::Union{Int, UnitRange}, g::G, pk::G, value::Int, ::Verifier; 𝐺)::Simulator` which uses `rangecommit` and also provides proof of correct ElGamal encryption where used randmization factors for `a` and `b` are the same.

## SecretSharing

Verifiable secret sharing. Comming soon...

## CommitmentShuffle

Commitment shuffle lays out a new shuffle protocol (I am not aware of it's previous uses) that uses generalized pedersen commitments. In contrast to `ShuffleProofs` it is interactive, however, interactivity is asynchronous and it provides information-theoretic security for a shuffle that is sometimes needed fto ensuring ever lasting privacy in case a new cryptograhic breaking algorithm surfaces or cryptographic relevant qauntuim computer ever gets built in the future. Another benefit of the shuffle is that it's outputs are unstructured and can contain anything allowing easy cryptographic protocol composition. The procol is:

1. Setup:
   - A verifiable generator list is established
   - A blinding generator 'h' is set

2. Dealer-member interaction:
   - Dealer sends a verifiably random generator g_i to each member
   - Member generates x_i and β_i
   - Member computes:
     * u_i <- g_i^x
     * C = h^β * u_i
     * PoK{(x): u_i = g_i^x_i)
   - Member sends back to dealer:
     * Signed {C}
     * β_i
     * u_i
     * PoK{(x): u_i <- g_i^x_i)
   - Dealer publishes the commitment on a public bulletin board

3. Dealer's consistency proof:
   - Dealer generates a secret vector r_i
   - Computes A <- h^r * ∏ u_i^s_i
   - Computes e_i from anouncement A using Fiat-Shamir transform
   - Computes secrets:
     * z = r + \sum_i \beta_i * e_i
     * w_i = s_i + e_i 
   - Announces on public bulletin board:
     * Shuffled list of (u_i, g_i, PoK{(x_i): u_i = g_i^x_i}, w_i) and anouncement A, z

4. Verification process:
   - Verify that every g_i was generated verifiably random
   - Verify PoK for every generator used in the commitment proof PoK{(x): u_i = g_i^x_i}
   - Compute e_i from A
   - Check that h^z * ∏ u_i^(s_i) = A * ∏ C_i^e_i

The second step can be made less interactive if member instead picks a random seed and generates the generator with it locally and deliver back the seed to the dealer. This scheme is also very convinient to be used for implemetning receipt freeness and coercion resistance that will be discloused shortly in `TallyProofs.jl`. 

To use the protocol we every member creates a commitment with `commit` method that is provided:
```
m = g^42
row::CommittedRow, C::G, β::BigItn = commit(m, g::G, h::G, verifier)
```
where `g` is unique generator provided to the member by the dealer and `m` will is a committed message. The commitment is signed by the member and the triple is delivered to the dealer over confidnetial channel. The dealer checks that `C = h^β * u`, `PoK{(x): u <- g^x}` and that `g` is an independent generator provided exlusivelly for the member (publically there is no link between the independent generator and the member's identity). 

When the collection period closes the dealer shuffles the resulting commitments and anounces shuffled rows along with a shuffle proof which can be produces via:

```
simulator = shuffle(rows, h, 𝐂, 𝛃, verifier)
verify(simulator) # true
```
The essence of the proof is that it checks that every generator is indpendent and that every commitment has a unique generator preventing substitution or removal and that the `PoK{(x): u <- g^x}` which ensures that `u` is indepent generator provided that `g` signs the message `m` that is passed as suffix to the verifier challenge to the `Schnorr` proof and hence signs it.

## Related Work

There is a substatntial work done in the literature for automating protocol scheme generation [1, 2]. This is interesting endavour, however, it does sacrifdice the ability to specify resulting protocol whoe would want to implement verification of the proofs independently with the spirit of software independence. 

For instance Schor protocol for provong knowledge for a list of tuples `(g_i, y_i)` can be either written as
```
PoK{(x_1,...,x_N): ∧_i y_i <- g_i^x_i}
```
or as
```
∧_i PoK{x_i: y_i <- g_i^x_i}
```
proving the same thing. The difference is that in the first case one would use a challenge that lists all inputs in the protocol wheras in the second case every challenge is compputed seperatelly from the inputs. 

Choices like theese general compilar makes makes it much harder for one from making an independent verifier for the proofs and their specification. Perhaps one could write a specification for the compiler instead then, but at the present to my knowledge such compilers are unable to produce more complex proofs bulletproofs or proofs of shuffle which need to be added add hoc. So their applicability is limited and one would still need to return to the pen and paper implementation and then implement it. Nevertheless such proof systems can be a valuable tool for finding out and experimenting with new protocol designs.

- [1] Lueks, Wouter et al. zksk: A Library for Composable Zero-Knowledge Proofs. Proceedings of the 18th ACM Workshop on Privacy in the Electronic Society (2019)
- [2] J. B. Almeida, E. Bangerter, M. Barbosa, S. Krenn, A.-R. Sadeghi, T. Schneider. A Certifying Compiler for Zero-Knowledge Proofs of Knowledge Based on Sigma Protocols. In 15th European Symposium on Research in Computer Security (2010)

Other more specialized proofs exist. For instance currently the state of the art range proofs are are made with bulletproofs [3, 4]. In contrast to provided implementation within `SigmaProofs` their proofs are in logarithmic of the range bitlength wheras here it grows linear with bitrange size. This can be useful for reducoing the size for identification schemes or auctions, but may not be what one needs for homomorphic evoting systems where the ranges are small.

- [3] Bünz, B., Bootle, J., Boneh, D., Poelstra, A., Wuille, P., & Maxwell, G. Bulletproofs: Short Proofs for Confidential Transactions and More. IEEE Symposium on Security and Privacy (2018)
- [4] BulletProofs implementation in Rust https://doc.dalek.rs/bulletproofs/

The SigmaProofs implements Verificatum verifier, parser along with independent generator basis generation that is specified in [5]. The proof of knowledge proofs for logarithm are well explained in lecture notes which I highly recomend anyone starting out their zero knowledge proofs journey [6]. The bit range proofs are implemented according to [7]. The secret sharing is being implemented according to [8]. There is a good overview of zero knowledge proofs used in evoting which one can fairly easy implement with SigmaProofs offered infrastructure [

- [5] Wikstrom, D. How To Implement A Stand-Alone Veriﬁer for the Veriﬁcatum Mix-Net. 
- [6] Schoenmakers, B. Lecture Notes Cryptographic Protocols (Version 1.9). Department of Mathematics and Computer Science, Technical University of Eindhoven. (2024)
- [7] Ronald Cramer, Rosario Gennaro, and Berry Schoenmakers. A secure and optimally efficient multi-authority election scheme. In Proceedings of the 16th annual international conference on Theory and application of cryptographic techniques (1997) https://link.springer.com/chapter/10.1007/3-540-69053-0_9
- [8] Feldman, P. A practical scheme for non-interactive verifiable secret sharing. In 28th Annual Symposium on Foundations of Computer Science (1987) (pp. 427-438). IEEE. https://www.cs.umd.edu/~gasarch/TOPICS/secretsharing/feldmanVSS.pdf
- [9] Smith, W.D. Cryptography meets voting. (2005)
