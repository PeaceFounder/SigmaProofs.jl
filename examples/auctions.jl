# TODO: RANGE PROOFS ARE NOT YET IMPLEMENTED

# Auctions: [AW13] uses range proofs for verifiable auctions. Range proofs help an auctioneer to prove to an auditor that the sale price was set correctly without revealing the values of the bids. For example, in a second-price auction with 
# n n bids, (where the sale price is equal to the second-highest bid), the auctioneer can provide proofs that n 1−1 bids were at most the sale price and one bid was greater than the sale price


# The setup is that the Dealer registers participant public keys which are used to sign auction bids (which we shall skip). The bids themselves are ElGamal encrypted under an authorithy issued public key.

# (1) Keygen of authorithy, providing pk
# (3) Bidders make a bids encrypted in ElGamal texts. Additionally proof of knowledge for the exponent can be provided if the bidding is made public
# (4) Authorithy selects highest bidder and decrypts the second highest bid and provides decryption ZKP
# (5) Now for every single bid the authorithy makes a range proof proving that it's value is lower than that of the winning bid. Before we can do so the authorithy needs to reencrypt ElGamal cyphertexts with their own exponent which it can prove to encrypt the same plaintext with plaintext equivalence test Dec((a, b)/(a', b')) = 1. Then one can proceed with NRange proofs as desired. 


sk, pk = keygen(g)
𝐺 = basis_generators[1]

function bid(value)
    
    α = rand(2:order(G)-1)

    a = g^α
    b = pk^α * 𝐺^value

    return (a, b)
end


function dec((a, b))

    m = b / a^sk
    
    isone(m) && return 0

    for i in 1:30
        𝐺^i == m && return i
    end

    error("Value not in range") # In practice thoose are decrypted as a proof
end


# Made bids by third parties. In real situation they are signed. May also require knowledge proof of exponenent to avoid Pfitzman attack, but it is unpractical to execute it as only the winners value is decrypted.

v_A = 10
bid_A = bid(v_A)

v_B = 20
bid_B = bid(v_B)

v_C = 15
bid_C = bid(v_C)

# The dealer decrypts every bid privatelly:

@test dec(bid_A) == v_A
@test dec(bid_B) == v_B
@test dec(bid_C) == v_C

# It sees that bid_B is the highest and hence had won. It needs to pay second largest bid bid_C. Now it needs to prove that it had acted honestly which can be done with range proofs. Before such proofs can be executed we need to make a substitutes.

α_A = rand(2:order(G)-1)
substitute_A = substitute(g, pk, bid_A..., sk, α_A, verifier)

α_B = rand(2:order(G)-1)
substitute_B = substitute(g, pk, bid_B..., sk, α_B, verifier)

decryption_C = decrypt(g, bid_C, sk, verifer)

C_C = 𝐺^v_C # α = 0
range_BC = rangecommit(4, g, pk, v_B - v_C, verifier; α = α_B)
range_CA = rangecommit(4, g, pk, v_C - v_A, verifier; α = -α_A)

### The auditor then can do the audit as follows

v_C = dec(decryption_C)
C_C = 𝐺^v_C 
C_A = substitute_A.b′
C_B = substitute_B.b′

@test range_A.proposition.y == C_B / C_C
@test range_A.proposition.y == C_C / C_A

@test verify(substitute_A) 
@test verify(substitute_B) 
@test verify(decryption_C) 

@test verify(range_BC)
@test verify(range_CA)
