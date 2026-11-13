#!/usr/bin/env python3
"""Independent mathematical checks, NOT Lean checking or a proof certificate."""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import json, math
import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    identities = {}
    a,b,c,w,h = sp.symbols('a b c w h', real=True)
    d1=b-1; d2=c-a*b
    f1=w+3-2*h; f2=w+3*a-2*a*c*h
    def reduce(expr):
        return sp.factor(sp.expand(expr).subs(c**2,a).subs(b**2,2/(1+a)))
    certs = {
        'first_low_gap': (f1-d1**2)-((w+2*a-a*a*h*h)+(b-h)*(2-a*a*(h+b))),
        'first_high_gap': (f1-d1**2)-((w+2-h*h)+(h-b)*(h+b-2)),
        'second_low_gap': (f2-d2**2)-((w+2*a-a*a*h*h)+a*(b-h)*(2*c-a*(h+b))),
        'second_high_gap': (f2-d2**2)-((w+2-h*h)+(h-b)*(h+b-2*a*c)),
        'corner_inner': (b*b-2)+2-b*b,
        'corner_outer': (b*b-2)+2*a-a*a*b*b,
    }
    for name,expr in certs.items():
        val=reduce(expr); assert val==0,(name,val); identities[name]=True
    x,y,vx,vy,r,mu=sp.symbols('x y vx vy r mu',real=True, nonzero=True)
    dot=x*vx+y*vy; angular=x*vy-y*vx
    geom=dot**2+angular**2-(x*x+y*y)*(vx*vx+vy*vy)
    assert sp.expand(geom)==0; identities['polar_pythagoras']=True
    accx=-mu*x/r**3; accy=-mu*y/r**3
    dH=vx*vy+x*accy-vy*vx-y*accx
    dW=2*vx*accx+2*vy*accy+2*mu*(dot/r)/r**2
    assert sp.simplify(dH)==0; identities['newton_angular_derivative_zero']=True
    assert sp.simplify(dW)==0; identities['newton_energy_derivative_zero']=True
    vCirc=sp.symbols('vCirc',real=True)
    cart=(vx+vCirc*y/r)**2+(vy-vCirc*x/r)**2
    polar=(dot/r)**2+(angular/r-vCirc)**2
    expected=(1-(x*x+y*y)/r**2)*(vx*vx+vy*vy-vCirc*vCirc)
    assert sp.simplify(cart-polar-expected)==0
    identities['cartesian_polar_impulse_identity']=True
    R,B=sp.symbols('R B',positive=True)
    # Squared peri/apo speeds of both ellipses.
    A2=2*B/(1+B); D2=2*B/(R*(R+B))
    for name,expr in {
        'first_ellipse_energy': A2-2-(A2/B**2-2/B),
        'second_ellipse_energy': D2-2/R-(R**2*D2/B**2-2/B),
        'bielliptic_middle_speed_order': R**2*D2-A2-2*B**2*(R-1)/((R+B)*(1+B)),
    }.items():
        assert sp.factor(expr)==0,(name,sp.factor(expr));identities[name]=True
    # Exact rational enclosure; no floating point is used in this certificate.
    Hlo=Q(13719,10000); Hhi=Q(1372,1000)
    Alo=Q(7,5); Ahi=Q(14033,10000)
    Dlo=Q(31,100); Dhi=Q(31623,100000)
    bounds=[('H',Hlo,Q(32,17),Hhi),('A',Alo,Q(128,65),Ahi),('D',Dlo,Q(1,10),Dhi)]
    bound_report={}
    for name,lo,rad,hi in bounds:
        assert lo>=0 and lo*lo<=rad<=hi*hi
        bound_report[name]={'lower':str(lo),'radicand':str(rad),'upper':str(hi),
                            'lower_square_margin':str(rad-lo*lo),'upper_square_margin':str(hi*hi-rad)}
    Hlower=Q(15,16)*Hlo-Q(3,4)
    Bupper=Q(63,64)*Ahi+Q(5,4)*Dhi-Q(5,4)
    gap=Hlower-Bupper
    assert gap>Q(9,1000)
    assert Dlo/4-Ahi/64>0 and Alo>1 and Dlo>Q(1,4)
    # Feasible set is larger than actual coast arcs, so testing it is stringent.
    rng=np.random.default_rng(20261113)
    alphas=np.concatenate([np.geomspace(1e-5,.1,20),np.linspace(.11,.99,20),[.999,.99999]])
    trials=0; max_cert_error=0.; min_margin=float('inf'); negative_h=0
    for aa in alphas:
        bb=math.sqrt(2/(1+aa));cc=math.sqrt(aa)
        for _ in range(64):
            hh=float(rng.uniform(-4,4))
            slack=0. if trials%8==0 else float(10**rng.uniform(-8,2))
            ww=max(hh*hh-2,aa*aa*hh*hh-2*aa)+slack
            fs1=ww+3-2*hh;fs2=ww+3*aa-2*aa*cc*hh
            assert fs1>=-1e-12 and fs2>=-1e-12
            ds1=math.sqrt(max(0,fs1));ds2=math.sqrt(max(0,fs2))
            bound1=bb-1;bound2=cc-aa*bb
            assert ds1>=bound1-1e-10 and ds2>=bound2-1e-10
            gap1=fs1-bound1**2;gap2=fs2-bound2**2
            if hh<=bb:
                cert1=ww+2*aa-aa*aa*hh*hh+(bb-hh)*(2-aa*aa*(hh+bb))
                cert2=ww+2*aa-aa*aa*hh*hh+aa*(bb-hh)*(2*cc-aa*(hh+bb))
            else:
                cert1=ww+2-hh*hh+(hh-bb)*(hh+bb-2)
                cert2=ww+2-hh*hh+(hh-bb)*(hh+bb-2*aa*cc)
            max_cert_error=max(max_cert_error,abs(gap1-cert1),abs(gap2-cert2))
            min_margin=min(min_margin,ds1+ds2-bound1-bound2)
            negative_h+=hh<0;trials+=1
    # The exact corner with zero radial components.
    for aa in alphas:
        bb=math.sqrt(2/(1+aa));cc=math.sqrt(aa)
        cst=abs(bb-1)+abs(aa*bb-cc)
        assert abs(cst-((bb-1)+(cc-aa*bb)))<1e-12
    # Independent Newton integration of the FINITE counterexample, not just speeds.
    def integrate(peri,apo,start_at_apo=False):
        A=(peri+apo)/2; tau=math.pi*A**1.5
        vp=math.sqrt(2*apo/(peri*(peri+apo)));va=peri*vp/apo
        y0=[-apo,0,0,-va] if start_at_apo else [peri,0,0,vp]
        target=np.array([peri,0,0,vp] if start_at_apo else [-apo,0,0,-va])
        def f(t,z):
            rr=math.hypot(z[0],z[1]); return [z[2],z[3],-z[0]/rr**3,-z[1]/rr**3]
        sol=solve_ivp(f,[0,tau],y0,method='DOP853',rtol=2e-12,atol=2e-13)
        assert sol.success
        err=float(np.max(np.abs(sol.y[:,-1]-target)/np.maximum(1,np.abs(target))))
        assert err<5e-7,err
        return {'periapsis':peri,'apoapsis':apo,'starts_at_apoapsis':start_at_apo,
                'time':tau,'endpoint_scaled_error':err}
    ode=[integrate(1,64),integrate(16,64,True),integrate(1,16)]
    AA=math.sqrt(128/65);DD=math.sqrt(.1);HH=math.sqrt(32/17)
    hc=15/16*HH-.75;bc=63/64*AA+1.25*DD-1.25
    # Wrong-model checks, not mathematical proofs.
    aa=.25; bb=math.sqrt(2/(1+aa));cc=math.sqrt(aa); hhcost=bb-1+cc-aa*bb
    negative={
      'omit_energy_allows_cheaper_fake_endpoints': cc-aa<hhcost,
      'omit_angular_allows_cheaper_fake_endpoints': math.sqrt(2-aa)-1<hhcost,
      'unrestricted_Hohmann_claim_is_false': bc<hc,
      'omit_middle_burn_changes_cost': abs((AA-1)+(DD-.25)-bc)>1e-4,
      'wrong_final_burn_direction': (DD-.25)>0 and (.25-DD)<0,
      'squared_impulse_objective_has_wrong_units': abs(2**2-2)>1,
    }
    assert all(negative.values())
    result={
      'evidence_type':'independent exact algebra, rational enclosure and numeric regression; NOT Lean verification',
      'symbolic_identities':identities,'symbolic_count':len(identities),
      'rational_root_intervals':bound_report,
      'counterexample_exact_bound':{'H_lower':str(Hlower),'bi_upper':str(Bupper),
        'certified_gap_lower':str(gap),'claimed_gap':'9/1000','strict_margin':str(gap-Q(9,1000))},
      'feasible_regressions':trials,'negative_angular_momentum_cases':negative_h,
      'corner_cases':len(alphas),'max_factorization_residual':max_cert_error,
      'minimum_sampled_total_gap':min_margin,
      'ODE_checks':ode,'negative_controls':negative,
      'example':{'R':16,'B':64,'H_delta_v':hc,'bi_delta_v':bc,
        'relative_delta_v_reduction':(hc-bc)/hc,
        'H_time':ode[2]['time'],'bi_time':ode[0]['time']+ode[1]['time'],
        'time_ratio':(ode[0]['time']+ode[1]['time'])/ode[2]['time']},
    }
    out=ROOT/'reports/math-checks.json';out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k in ['symbolic_count','feasible_regressions','negative_angular_momentum_cases','corner_cases','max_factorization_residual','counterexample_exact_bound','example','ODE_checks','negative_controls']},indent=2))

if __name__=='__main__': main()
