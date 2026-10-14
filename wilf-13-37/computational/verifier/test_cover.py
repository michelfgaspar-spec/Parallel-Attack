"""Meaningful alternate matching/propagation/domain adversarial checks."""
import itertools,random,unittest
import arithmetic as A
import cover as C


def matching_brute(edges):
    def visit(i,used):
        if i==len(edges):return 0
        return max([visit(i+1,used)]+[1+visit(i+1,used|{v}) for v in edges[i] if v not in used])
    return visit(0,set())

class Checks(unittest.TestCase):
    def test_joint_and_residue_maximum(self):
        rng=random.Random(20261003)
        fixtures=[[(2,2),(2,2)],[(2,3),(1,2),(1,1)],[(4,6),(0,0),(5,5)],[],[(0,0)]*3]
        for _ in range(150):fixtures.append([(rng.randrange(-3,4),rng.randrange(0,5)) for _ in range(rng.randrange(7))])
        for intervals in fixtures:
            self.assertEqual(C.interval_matching(intervals),matching_brute([set(range(a,b+1)) for a,b in intervals]))
            for m in (2,3,5):self.assertEqual(C.residue_matching(intervals,m),matching_brute([{x%m for x in range(a,b+1)} for a,b in intervals]))
    def test_multiplicity_and_negative_numerator(self):
        # Exhaust actual assignments satisfying independently evaluated constraints.
        for u in ((0,0,0),(0,0,1),(0,1,1),(1,1,1)):
            for level in range(2,5):
                m=5;rho=3;L=[-2,0];U=[9,13];levels=(1,1)
                actual=[x for x in itertools.product(range(-2,10),range(14)) if x[0]<x[1] and level*m-rho<=sum(x[i] for i in u)<(level+1)*m-rho]
                box=C.propagate(levels,L,U,[(u,level)],m,rho)
                if actual:
                    self.assertIsNotNone(box)
                    for x in actual:self.assertTrue(all(a<=v<=b for a,v,b in zip(box[0],x,box[1])))
    def test_alpha_domain_independent_product(self):
        for n in range(14,38):
            for q in range(4,n//3+1):
                weights=list(range(q-1,0,-1));r=n-q
                got=list(A.profiles(n,q))
                # Independent coefficient convolution counts domain points.
                ways=[0]*(r+1);ways[0]=1
                for w in weights:
                    for v in range(w,r+1):ways[v]+=ways[v-w]
                self.assertEqual(len(got),ways[r]);self.assertEqual(len(got),len(set(got)))
                self.assertTrue(all(sum(a*w for a,w in zip(z,weights))==r for z in got))
    def test_strict_endpoint(self):
        for n in range(14,38):
            for q in range(4,n//3+1):
                for F in range(20):
                    sigma,E,Cmax=C.endpoint(n,q,F,0)
                    self.assertEqual(E,(sigma-1)//(n-q))
                    self.assertTrue((n-q)*E<sigma)
                    self.assertTrue((n-q)*(E+1)>=sigma)
    def test_full_e_slots_and_zero_rho(self):
        # e=7 has one right-primitive slot when s=5. No e=1+s equation.
        row={'n':35,'q':5,'F':60,'N':60,'kappa':(0,0,0,0),'Emin':6,'E':8,'sigma':300,'allocation_id':0}
        class Sink:
            def emit(self,*a,**k):return 0
        params=list(C.integer_parameters(row,Sink()))
        self.assertTrue(any(e==7 for (e,d,m,r,c),event in params))
        # rho0 is not dropped from the exact domain.
        row.update(n=14,q=4,F=100,N=100,Emin=4,E=4,sigma=400,kappa=(0,0,0))
        self.assertTrue(any(p[3]==0 for p,event in C.integer_parameters(row,Sink())))
    def test_all_degree_divisors(self):
        self.assertEqual(C.divisors((0,0,1,1)),[(0,0,1),(0,1,1)])
        self.assertEqual(C.divisors((0,0,0,0)),[(0,0,0)])
        self.assertEqual(A.growth(0,4),0)
        self.assertEqual(A.growth(3,5),3)

if __name__=='__main__':unittest.main()
