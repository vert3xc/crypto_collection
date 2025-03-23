
def bsgs_ecdlp(P, Q):
    m = ceil(sqrt(P.order()))
    # Baby Steps: Lookup Table
    lookup_table = {j*P: j for j in range(m)}
    # Giant Step
    for i in range(m):
        temp = Q - (i*m)*P
        if temp in lookup_table:
            return (i*m + lookup_table[temp]) % P.order()
    return None


def pohlig_hellman_point(P,Q):
     zList = list()
     conjList = list()
     rootList = list()
     n = P.order()
     factorList = list(n.factor())[:-1]
     for facTuple in factorList:
         P0 = (ZZ(n/facTuple[0]))*P
         conjList.append(0)
         rootList.append(facTuple[0]^facTuple[1])
         for i in range(facTuple[1]):
             Qpart = Q
             for j in range(1,i+1):
                 Qpart = Qpart -(zList[j-1]*(facTuple[0]^(j-1))*P)
             Qi = (ZZ(n/(facTuple[0]^(i+1))))*Qpart
             zList.insert(i,discrete_log(Qi,P0,operation='+'))
             conjList[-1] = conjList[-1] + zList[i]*(facTuple[0]^i)
     return crt(conjList,rootList)


def pohlig_hellman_numbers(P, H):
    n = P.multiplicative_order()
    factors = list(n.factor())[:-1]
    residues = []
    moduli = []
    for ft in factors:
        pi = P ** (n // ft[0])
        hi = H ** (n // ft[0])
        moduli.append(ft[0])
        residues.append(discrete_log(hi, pi))
    return crt(residues, moduli)
