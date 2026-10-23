# Numerical check of the stage Jacobian in Theorem svl(i):
# with n_{R<t} held fixed, the map q_{P_t} -> n_{C_t} has |det dn/dq| = |det S_t| prod n / prod q.
import random, math
def solve(A, b):
    n = len(A); M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for c in range(n):
        p = max(range(c, n), key=lambda i: abs(M[i][c])); M[c], M[p] = M[p], M[c]
        for i in range(n):
            if i != c:
                f = M[i][c]/M[c][c]; M[i] = [a - f*bb for a, bb in zip(M[i], M[c])]
    return [M[i][n]/M[i][i] for i in range(n)]
def det(A):
    A = [r[:] for r in A]; n = len(A); d = 1.0
    for c in range(n):
        p = max(range(c, n), key=lambda i: abs(A[i][c]))
        if abs(A[p][c]) < 1e-300: return 0.0
        if p != c: A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for i in range(c+1, n):
            f = A[i][c]/A[c][c]; A[i] = [a - f*b for a, b in zip(A[i], A[c])]
    return d
random.seed(7); worst = 0; cnt = 0
while cnt < 300:
    a, b = random.randint(1, 3), random.randint(1, 3)   # |P_<t| = |R_<t| = a, |P_t| = |C_t| = b
    E = [[random.choice([0, 0, 1, 2, 3]) for _ in range(a+b)] for _ in range(a+b)]  # rows: R_<t then C_t; cols: P_<t then P_t
    Eold = [r[:a] for r in E[:a]]
    if abs(det(Eold)) < 0.5 or abs(det(E)) < 0.5: continue
    logc = [random.uniform(0, 3) for _ in range(a+b)]
    lognR = [random.uniform(5, 8) for _ in range(a)]
    def nC(xPt):
        # solve for x_{P<t} from rows R_<t, then evaluate rows C_t
        rhs = [lognR[i] - logc[i] - sum(E[i][a+j]*xPt[j] for j in range(b)) for i in range(a)]
        xold = solve(Eold, rhs)
        x = xold + list(xPt)
        return [logc[a+i] + sum(E[a+i][j]*x[j] for j in range(a+b)) for i in range(b)], x
    xPt = [random.uniform(1, 3) for _ in range(b)]
    ln0, x0 = nC(xPt)
    h = 1e-6
    J = []
    for j in range(b):
        qp = [math.exp(v) for v in xPt]; qp2 = qp[:]; qp2[j] += h; qm = qp[:]; qm[j] -= h
        lp, _ = nC([math.log(v) for v in qp2]); lm, _ = nC([math.log(v) for v in qm])
        J.append([(math.exp(lp[i]) - math.exp(lm[i]))/(2*h) for i in range(b)])
    Jt = [[J[j][i] for j in range(b)] for i in range(b)]
    # Schur complement S = E_{C,Pt} - E_{C,P<} E_{R<,P<}^{-1} E_{R<,Pt}
    S = []
    for i in range(b):
        row = []
        for j in range(b):
            col = solve(Eold, [E[r][a+j] for r in range(a)])
            row.append(E[a+i][a+j] - sum(E[a+i][r]*col[r] for r in range(a)))
        S.append(row)
    pred = abs(det(S)) * math.prod(math.exp(v) for v in ln0) / math.prod(math.exp(v) for v in xPt)
    got = abs(det(Jt))
    rel = abs(got - pred)/pred
    worst = max(worst, rel); cnt += 1
    assert abs(abs(det(E)) - abs(det(Eold))*abs(det(S))) < 1e-6 * max(1, abs(det(E)))
print("stage Jacobian: %d random cases, max relative error %.2e; det E = det E_old * det S verified" % (cnt, worst))
