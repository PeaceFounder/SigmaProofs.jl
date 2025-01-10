# SigmaProofs.jl

[![codecov](https://codecov.io/gh/PeaceFounder/SigmaProofs.jl/graph/badge.svg?token=6LUFS7ZZPE)](https://codecov.io/gh/PeaceFounder/SigmaProofs.jl)

SigmaProofs.jl is a comprehensive toolkit for implementing cryptographic protocols that utilize group-based zero-knowledge proofs. The package specializes in proofs with a commitment-challenge-reply structure and includes a Verificatum-compatible parser for handling challenges and managing simulator serialization/deserialization. It also provides an easy-to-use ElGamal implementation, essential for reencryption mixnets as used in ShuffleProofs.jl.

## Core Architecture

The package employs a verifier-agnostic design that facilitates exploration of proof specifications and generator basis algorithms. Each proof is implemented as a simulator consisting of three components:

- A `Proposition` defining the statement to be proved
- A `Proof` supporting the statement
- A `Verifier` participating in proof generation and validation

While proofs are typically made non-interactive through Fiat-Shamir transformation, interactive proofs are also supported through the same codebase, leveraging Julia's unique handling of asynchronous functions.

The package implements several core methods that form the foundation of its zero-knowledge proof system:

* `prove(::Proposition, secrets..., ::Verifier)::Proof`
  - Generates a proof for a given proposition using provided secret values
  - Takes a proposition defining what to prove, the secret values needed for the proof, and a verifier
  - Returns a proof object that can be verified by others

* `challenge(::Verifier, ::Proposition, args...)` 
  - Generates a challenge for interactive or Fiat-Shamir transformed proofs
  - Used by the verifier to ensure the prover knows the claimed secrets
  - Takes additional arguments specific to the proof type being constructed

* `verify(::Proposition, ::Proof, ::Verifier)::Bool`
  - Validates whether a proof correctly demonstrates the proposition
  - Returns true only if the proof is valid for the given proposition
  - Doesn't require knowledge of any secret values

* `proof_type(::Type{<:Proposition})::Type{<:Proof}`
  - Maps proposition types to their corresponding proof types
  - Enables generic programming with different proof systems
  - Helps maintain type safety across the proving system

For convenience, most proposition types provide construction methods with the signature:
```julia
construct(args..., secrets..., ::Verifier)::Simulator
```
These methods package together the proposition, proof, and verifier into a simulator object for easier handling.

The package also provides generator creation functionality:
```julia
generator_basis(::Verifier, ::Type{<:Group}, N)::Vector{G}
```
This method produces a vector of independent generators, crucial for creating Pedersen commitments and other cryptographic constructions where generator independence is required for security.

## LogProofs

LogProofs forms the foundation of zero-knowledge proofs in the package, implementing both Schnorr and Chaum-Pedersen proofs. The Schnorr proof demonstrates knowledge of an exponent linking two public group elements (g, y) with the statement `PK{(x): y <- g^x}`. When combined with a suffix message in the challenge, it creates the Schnorr Signature. The Chaum-Pedersen proof extends this to prove that a list of pairs (g_i, y_i) shares the same exponent: `PK{(x): A_i y_i <- g_i^x}`.

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

## ElGamal and Decryption Proofs

The package provides a robust implementation of ElGamal encryption through the `ElGamalRow` type, supporting both standard and generalized ElGamal ciphertexts. Messages can be conveniently encrypted using the `Enc` type and decrypted with `Dec`.

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
dec(ciphertext) == plaintexts # true
width(ciphertext) == 2 

# Arithmetic operations
dec(ciphertext * ciphertext) == plaintexts .* plaintexts
dec(ciphertext ^ 7) == plaintexts .^ 7
dec(ciphertext / enc(ciphertext, r)) == (one(g), one(g))
```

The DecryptionProofs module extends Chaum-Pedersen proofs to handle ElGamal ciphertext vectors and generate zero-knowledge proofs of correct decryption:

```julia
using CryptoGroups
using SigmaProofs.ElGamal: Enc
using SigmaProofs.DecryptionProofs: exponentiate, verify

g = @ECGroup{P_192}()
verifier = ProtocolSpec(; g)

sk = 123
pk = g^sk

encryptor = Enc(pk, g)

plaintexts = [g^4, g^2, g^3] .|> tuple
cyphertexts = encryptor(plaintexts, rand(2:order(g)-1, length(plaintexts)))

simulator = decrypt(g, cyphertexts, sk, verifier)

verify(simulator) # true
simulator.proposition.plaintexts == plaintexts
```

The arithmetic operations on ElGamal ciphertexts enable the construction of plaintext equivalence tests (PET), a crucial tool in cryptographic protocols. To test if two ciphertexts encode the same plaintext without decrypting them, one can divide the ciphertexts and prove that the result encrypts the identity element. This is implemented by reencrypting the quotient with a fresh random value and providing a zero-knowledge proof that the reencryption decrypts to one(g). This technique is particularly valuable in voting systems for detecting duplicate votes or in anonymous credential systems for revocation checks.

## Range Proofs

Range proofs enable verification that an integer within a ciphertext or commitment falls within a specified range without revealing the value. The package implements several range proof variants, from simple bit encoding to n-ary decomposition for arbitrary ranges. These proofs serve as fundamental building blocks for various cryptographic applications including identity-based signatures, sealed bid auctions, and homomorphic tallying in e-voting systems.

The simplest method, `bitenc`, proves that an ElGamal ciphertext encodes either 0 or 1, implementing the statement `(g^r, pk^r * 𝐺) OR (g^r, pk^r / 𝐺)` without revealing `r`:

```julia
simulator = bitenc(g, pk, true, verifier)
verify(simulator) # true
```

For commitment-focused applications, `bitcommit` provides a more efficient alternative using Pedersen commitments:

```julia
simulator = bitcommit(g, h, value, verifier)
verify(simulator) # true
```

The package extends these basic proofs to handle arbitrary ranges through n-ary decomposition with `rangecommit`:

```julia
# For range 0 <= value < 2^n
simulator = rangecommit(n, g, h, value, verifier)

# For arbitrary ranges
simulator = rangecommit(0:100, g, h, value, verifier)
```

These range commitments enable powerful applications in identity-based systems. For example, a client can generate a commitment `C = h^β * g^v` encoding personal data (like birth date or location), which an identity provider signs. The client can later prove age requirements or geographic location to service providers without revealing exact values.

For sealed bid auctions, particularly Vickrey auctions where the highest bidder wins but pays the second-highest price, the package provides specialized functionality:

```julia
# Dealer processes collected bids and proves winner
simulator = vickrey_auction(bids, g, h, 𝛃, verifier)
verify(simulator) # true

(; winner, value_win) = simulator.proposition
```

The framework also supports range proofs for homomorphic tallying in e-voting systems. The `rangeenc` function ensures votes are honestly cast within allowed ranges:

```julia
# For simple yes/no voting
simulator = bitenc(g, pk, vote, verifier)

# For multiple options
simulator = rangeenc(range, g, pk, vote, verifier; 𝐺)
```

These range proofs work in conjunction with homomorphic tallying methods where individual votes remain encrypted while allowing computation of the final tally through threshold decryption ceremonies. The proofs ensure vote validity without compromising voter privacy.


## Secret Sharing

The SecretSharing module implements a robust and secure version of Feldman's Verifiable Secret Sharing (VSS) scheme, which enhances the classical Shamir's Secret Sharing with crucial verification capabilities. This implementation enables a trusted dealer to distribute shares of a sensitive secret among multiple participants while simultaneously providing them with cryptographic proofs to verify their shares' validity. This verification process ensures that when the time comes to reconstruct the secret, all valid shares will contribute to recreating the exact same secret, preventing both malicious participants and potential dealer misconduct.

At its core, the scheme operates by embedding the secret as the first coefficient of a polynomial, with the remaining coefficients generated randomly to ensure security. The dealer then evaluates this polynomial at different points to create unique shares for each participant. What sets VSS apart from basic secret sharing is the addition of public commitments to the polynomial coefficients, allowing participants to verify their shares' correctness without compromising the scheme's security properties.

Here's a comprehensive example demonstrating the VSS protocol implementation:

```julia
using CryptoGroups
using SigmaProofs.SecretSharing
using SigmaProofs.Verificatum

# Initialize the group and verifier
G = @ECGroup{P_192}
g = G()
verifier = ProtocolSpec(; g)

# Setup parameters
N = 5  # Number of participants
M = 3  # Threshold (minimum participants needed for reconstruction)

# Generate participant nodes and polynomial coefficients
nodes = rand(2:order(G) - 1, N) 
coeff = rand(2:order(G) - 1, M)

# Generate shares using polynomial evaluation
d_vec = evaluate_poly(nodes, coeff, order(G))

# Create and verify the sharing setup
setup = sharding_setup(g, nodes, coeff, verifier; d_vec)
verify(setup) # true
```

The polynomial evaluation at different nodes creates shares that can be used to reconstruct the secret (first coefficient) through Lagrange interpolation. This mathematical foundation ensures that only groups of participants meeting or exceeding the threshold can successfully reconstruct the secret:

```julia
# Minimum threshold reconstruction
l_vec = lagrange_coef(nodes[1:M], order(G))
mod(sum(d_vec[1:M] .* l_vec), order(G)) == first(coeff)

# Can be constructed all shards
l_vec = lagrange_coef(nodes, order(G))
mod(sum(d_vec .* l_vec), order(G)) == first(coeff)
```

One of the most powerful applications of VSS lies in distributed cryptographic operations, particularly in threshold cryptography. Each participant's verified share `(ni, di)` can contribute to joint operations like distributed signing or decryption, where the group's public key is derived from the shared secret `pk = g^first(coeff)`. This enables robust threshold cryptographic operations without ever reconstructing the sensitive private key:

```julia
# The first coefficient is the secret
sk = first(coeff)
pk = g^sk

# Elements to be exponentiated
elements = [g^2, g^3, g^5]

# Each participant proves knowledge of their share
simulators = [exponentiate(g, elements, di, verifier) for (ni, di) in enumerate(d_vec)]
exponentiations = [s.proposition for s in simulators]
proofs = [s.proof for s in simulators]

# Merge shares to reconstruct the secret
full_exponentiation = merge_exponentiations(setup, elements, exponentiations, proofs)
verify(full_exponentiation) # true
```

This implementation finds critical applications in distributed systems requiring high security and trust distribution. For instance, in threshold encryption systems, the decryption key can be shared among multiple authorities, requiring collaboration for decryption while maintaining security even if some authorities are compromised. The module supports both threshold exponentiation and decryption operations through the same underlying principles, with specialized merge functions available for each use case. The implementation provides comprehensive verification at every step, ensuring that partial operations can be validated before final reconstruction or application.

The VSS scheme implemented here provides strong security guarantees through its information-theoretic security properties for the secret sharing aspect, combined with the computational security of the verification components. This makes it particularly suitable for long-term secure applications where trust distribution and verifiability are crucial requirements. For detailed implementations of specific applications like threshold decryption ceremonies, users are encouraged to examine the comprehensive test suite in `test/secretsharing.jl`, which provides additional examples and use cases.

## Generator Commitment Shuffle

The package introduces a novel shuffle protocol specifically designed for commitments using independent generators. Unlike generic commitment shuffles, this protocol assigns each participant a unique, independently generated base for their commitment. This interactive but asynchronous protocol provides information-theoretic security, making it particularly valuable for applications requiring long-term privacy guarantees against future cryptographic breakthroughs or quantum computing advances. The uniqueness of generators prevents malicious substitution of commitments while maintaining unlinkability of the shuffle outputs.

Here's a typical usage example:

```julia
# Member creates a commitment using their unique generator g
m = g^42
row, C, β = commit(m, g, h, verifier)  # g is unique for each member

# Dealer shuffles commitments and generates proof
simulator = shuffle(rows, h, 𝐂, 𝛃, verifier)
verify(simulator) # true
```

The protocol follows a four-phase process:

1. Setup phase where each participant receives a unique, verifiably generated base element g_i and a common blinding generator h
2. Dealer-member interaction where each member creates a commitment using their assigned generator and proves knowledge of the committed value
3. Dealer's consistency proof ensuring proper shuffling while preserving the binding between commitments and their unique generators
4. Verification process confirming both the validity of individual commitments and the integrity of the shuffle

The use of independent generators provides stronger security guarantees compared to generic commitment shuffles, as each commitment is intrinsically bound to its creator through the unique generator while maintaining privacy through the shuffle. This implementation is particularly suitable for receipt-freeness and coercion resistance in voting systems, with extended functionality available in the upcoming TallyProofs.jl package.

## Related Work and Design Considerations

While automated protocol scheme generation has been explored extensively in academic literature, SigmaProofs.jl prioritizes explicit protocol specification to facilitate independent verification. This design choice acknowledges the trade-off between automation and specification clarity, particularly important for security-critical applications.

For example, a Schnorr protocol proving knowledge for multiple tuples can be specified in two equivalent but distinct ways:
```
PoK{(x_1,...,x_N): ∧_i y_i <- g_i^x_i}
```
or
```
∧_i PoK{x_i: y_i <- g_i^x_i}
```

While both approaches prove the same statement, they differ in challenge computation methods, illustrating the importance of explicit protocol specification for independent verification.

The package incorporates established cryptographic techniques and builds upon significant prior work:

- Verificatum verifier implementation and parser following Wikström's specifications
- Zero-knowledge proof fundamentals based on Schoenmakers' comprehensive lecture notes
- Range proofs implementing Cramer, Gennaro, and Schoenmakers' secure election scheme
- Secret sharing following Feldman's practical VSS scheme
- Modern e-voting cryptography principles as outlined by Smith

For specific applications requiring optimized range proofs, alternatives like Bulletproofs offer logarithmic-size proofs compared to our linear implementation. However, our approach remains practical for small ranges common in e-voting systems and provides better composability with other protocols.

## Future Development

Future updates will focus on expanding the protocol suite while maintaining the package's commitment to explicit specification and independent verifiability. Planned developments include integration with TallyProofs.jl and enhanced support for complex cryptographic protocol composition.

For implementation details, examples, and test cases, please refer to the relevant test files in the repository.

## References

1. Lueks, Wouter et al. "zksk: A Library for Composable Zero-Knowledge Proofs." Proceedings of the 18th ACM Workshop on Privacy in the Electronic Society (2019).

2. J. B. Almeida, E. Bangerter, M. Barbosa, S. Krenn, A.-R. Sadeghi, T. Schneider. "A Certifying Compiler for Zero-Knowledge Proofs of Knowledge Based on Sigma Protocols." In 15th European Symposium on Research in Computer Security (2010).

3. Bünz, B., Bootle, J., Boneh, D., Poelstra, A., Wuille, P., & Maxwell, G. "Bulletproofs: Short Proofs for Confidential Transactions and More." IEEE Symposium on Security and Privacy (2018).

4. Wikström, D. "How To Implement A Stand-Alone Verifier for the Verificatum Mix-Net."

5. Schoenmakers, B. "Lecture Notes Cryptographic Protocols (Version 1.9)." Department of Mathematics and Computer Science, Technical University of Eindhoven. (2024).

6. Ronald Cramer, Rosario Gennaro, and Berry Schoenmakers. "A secure and optimally efficient multi-authority election scheme." In Proceedings of the 16th annual international conference on Theory and application of cryptographic techniques (EUROCRYPT'97). Springer-Verlag, Berlin, Heidelberg, 103–118.

7. Feldman, P. "A practical scheme for non-interactive verifiable secret sharing." In 28th Annual Symposium on Foundations of Computer Science (1987) (pp. 427-438). IEEE.

8. Smith, W.D. "Cryptography meets voting." (2005)








