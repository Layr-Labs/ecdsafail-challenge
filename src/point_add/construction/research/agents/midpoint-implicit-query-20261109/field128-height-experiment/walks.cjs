'use strict';

const { checkedSource } = require('./pinned.cjs');
const path = require('path');
const primitiveSource = checkedSource(
  path.resolve(__dirname, '../width109-handoff/emit109-reverse-digits.cjs'),
  '4cb72b84fa2b004d7b86dfe826a3d4183e23f4705cb589f83b432fa7eaf33cc4'
);
// The archived module exports only its specialized 109-bit emitter. Reuse its
// unchanged generic ripple, fused digit and dirty-control gates without changing it.
const [BaseWalk, digit] = Function('module', primitiveSource +
  '\nreturn [UnitWalk, digit];')({ exports: {} });

class HeightWalk extends BaseWalk {
  plan() {
    return this.heightPlan(false);
  }

  heightPlan(allowNonunits) {
    const n = this.n, L = this.L, R = this.R;
    const tag = this.tag, fire = [this.fire];
    const blocks = [];
    const emit = fn => blocks.push({ fn, rev: false });
    const rotation = (register, controls, direction) => {
      for (let j = 0; j < tag.length && (1 << j) < register.length; j++) {
        const shift = direction * (1 << j);
        emit(() => this.rot(controls.concat(tag[j]), register, shift));
      }
    };
    const normalize = (register, controls) => {
      for (let j = tag.length - 1; j >= 0; j--) {
        const shift = 1 << j;
        if (shift >= register.length) continue;
        emit(() => {
          this.zer(controls, register.slice(-shift), tag[j]);
          this.rot(controls.concat(tag[j]), register, shift);
        });
      }
    };
    const coefficient = (bank, size) =>
      Array.from({ length: size }, (_, j) => bank[n-j]);

    // Initially (A,r,u,v) = (modulus,min(x,modulus-x),0,1).
    const modulus = L.slice(0,n), residue = R.slice(0,n);
    emit(() => {
      const high = residue[n-1];
      this.op([high], this.sign);
      this.raw(-1,-1,high);
      this.lt([high], residue.slice(0,-1), modulus.slice(1), this.sign);
      this.raw(-1,-1,high);
    });
    emit(() => {
      for (const q of modulus) this.raw(-1,-1,q);
      this.add([this.sign], modulus, residue, 0, null);
      for (const q of modulus) this.raw(-1,-1,q);
      for (const q of residue) this.op([this.sign],q);
    });
    emit(() => this.raw(-1,-1,R[n]));

    for (let k = 0; k < n; k++) {
      const t = k+1, m = n-k;
      const A = L.slice(0,m), r = R.slice(0,m);
      const u = coefficient(L,t), v = coefficient(R,t);

      // On the coprime walk, r=0 first occurs at A=1. On the general
      // walk, a large terminal gcd may overlap the nominal coefficient.
      emit(() => {
        const candidate = () => {
          this.zer([], allowNonunits ? r : A.slice(1), this.tst);
          this.raw(-1,-1,this.tst);
        };
        candidate();
        this.lt([this.tst], A, r, this.fire);
        this.reverse(candidate);
      });
      if (k > 0 && k < n-1) {
        const prep = [this.tst];
        emit(() => {
          const quotientIsOne = () => {
            const high = r[m-1];
            this.op([high], this.aux);
            this.raw(-1,-1,high);
            this.lt([high], r.slice(0,-1), A.slice(1), this.aux);
            this.raw(-1,-1,high);
          };
          quotientIsOne();
          this.op([this.fire,this.aux], this.tst);
          for (const q of u) this.raw(-1,-1,q);
          this.lt([this.fire,this.aux], v, u, this.tst);
          for (const q of u) this.raw(-1,-1,q);
          this.reverse(quotientIsOne);
        });
        emit(() => {
          this.reverse(() => this.add(prep,r,A,this.cin,null));
          for (let j=0; j<m; j++) this.swap(prep,A[j],r[j]);
          this.add(prep,v,u,this.cin,null);
          for (let j=0; j<t; j++) this.swap(prep,u[j],v[j]);
          this.op(prep,this.sign);
        });
        emit(() => this.op(allowNonunits ? [this.fire,L[n-k]] : [L[n-k]], this.tst));
      }

      // Normalize the divisor. Its implicit leading one serves as the
      // first quotient carry. The remaining digits enter low A in rank order.
      normalize(r,fire);
      emit(() => {
        this.op(fire,r[m-1]);
        this.raw(-1,-1,this.aux);
        const gates = digit(m, r.slice(0,-1).concat(this.aux), A, r[m-1], this.fire, this.tst);
        for (const g of gates) this.raw(g.length===1 ? -1 : g[0], g.length===3 ? g[1] : -1, g[g.length-1]);
        this.raw(-1,-1,this.aux);
      });
      emit(() => this.op(fire,this.tst));
      for (let i=0; i<m-1; i++) emit(() => {
        this.multag(fire,i,[],this.tst);
        const run = [this.tst], divisor = r.slice(i+1);
        for (const q of A.slice(i)) this.swap(run,this.aux,q);
        this.raw(-1,-1,r[0]);
        this.restore(run,divisor.slice(0,-1).concat(r[0]),A.slice(i+1),0,this.aux);
        this.raw(-1,-1,r[0]);
        this.op(run.concat(this.aux),A[i]);
        this.op(run.concat(A[i]),this.aux);
      });
      emit(() => this.multag(fire,m-1,[],this.tst));

      // Consume the same live digits in reverse to assemble q*v+u.
      for (let i=m-2; i>=0; i--) emit(() => {
        this.multag(fire,i+1,[],this.tst);
        const run = [this.tst];
        this.reverse(() => this.restore(run,v,u,this.cin,A[i]));
        for (let j=t-1; j>=0; j--) this.swap(run,A[i],u[j]);
      });
      emit(() => {this.op(fire,this.tst);this.multag(fire,0,[],this.tst);});
      emit(() => {
        const carry = r[m-1];
        this.reverse(() => this.restore(fire,v,u,0,carry));
        for (let j=t-1; j>=0; j--) this.swap(fire,carry,u[j]);
        this.swap(fire,carry,L[m]);
        this.op(fire,carry);
      });

      // Two rotations replace the full permutation for every possible height.
      rotation(r,fire,-1);
      emit(() => this.rot(fire,L.slice(m,n+1),-1));
      rotation(L.slice(0,n+1),fire,-1);
      const valuationStart = blocks.length;
      normalize(r,fire);
      rotation(r,fire,-1);
      const valuation = blocks.splice(valuationStart);
      for (let j=valuation.length-1; j>=0; j--) blocks.push({fn:valuation[j].fn,rev:true});
      emit(() => {
        for (let j=0; j<=n; j++) this.swap(fire,L[j],R[j]);
        this.op(fire,this.sign);
        if (allowNonunits) {
          const nonempty = () => {
            this.zer([],R.slice(0,m+1),this.tst);
            this.raw(-1,-1,this.tst);
          };
          nonempty(); this.op([this.tst,L[n-k]],this.fire); this.reverse(nonempty);
        } else this.op([L[n-k]],this.fire);
      });
    }

    // Return the original generic walk's terminal layout. Keep a possibly
    // full-width gcd in the low left prefix during the coefficient shift.
    if (allowNonunits) {
      for (let bits=1; bits<=n; bits++) {
        const leftStart=n+1-bits, leading=R[n-bits+1], high=R.slice(1,n-bits+1);
        const match = () => this.zer([leading],high,this.fire);
        emit(match);
        emit(() => {
          for(let j=n; j>=leftStart; j--) this.swap(fire,L[j],L[j+1]);
        });
        emit(match);
      }
    }
    emit(() => {
      this.raw(-1,-1,this.sign);
      if (allowNonunits) for (let j=n; j>=1; j--) this.swap([],R[j],R[j+1]);
    });
    return blocks;
  }
}

class ReducedGcdWalk extends HeightWalk {
  plan() { return this.heightPlan(true); }
}

class CanonicalUnit extends HeightWalk {
  plan() {
    const blocks = super.plan(), n = this.n;
    const u = Array.from({length:n},(_,i)=>this.L[n-i]);
    const v = Array.from({length:n},(_,i)=>this.R[n-i]);
    blocks.push({ rev:false, fn:() => {
      this.zer([],v.slice(1),this.sign);
      for (const q of v) this.raw(-1,-1,q);
      this.add([this.sign],v,u,0,null);
      for (const q of v) this.raw(-1,-1,q);
      for (const q of u) this.op([this.sign],q);
      const high = u[n-1];
      this.op([high],this.sign);
      this.raw(-1,-1,high);
      this.lt([high],u.slice(0,-1),v.slice(1),this.sign);
      this.raw(-1,-1,high);
      this.raw(-1,-1,this.L[0]);
      for(let j=0; j<=n; j++) this.swap([],this.L[j],this.R[n-j]);
    }});
    return blocks;
  }
}

module.exports = { ReducedGcdWalk, CanonicalUnit };
