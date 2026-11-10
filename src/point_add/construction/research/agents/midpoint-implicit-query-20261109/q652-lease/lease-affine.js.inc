    affineProduct(tape,a,d,back){
        if(this.rankHost!==this.pick){super.affineProduct(tape,a,d,back);return;}
        const vTop=this.v[this.k];
        // A taken row has V[k]=1 throughout this subproduct. The fourth
        // shift tag starts at zero on an idle row, so this leaves pick clean.
        const park=rv=>{
            const ops=[()=>tape.out(NONE,this.take,vTop),
                dir=>this.permute(tape,[this.pick,vTop],[vTop,this.pick],[this.take],dir)];
            stepList(ops,rv,fn=>fn(rv));
        };
        park(false);
        const layer=Object.create(this);
        layer.tag=this.tag.slice();layer.tag[3]=vTop;layer.rankHost=vTop;
        layer.digit=MixedArithmetic.prototype.digit;
        layer.mixedHeld=(t,q,v,r,controls,reverse)=>{
            const enabled=controls.filter(c=>c!==t.one);
            layer.mixed(t,q,v,r,enabled,reverse);
        };
        super.affineProduct.call(layer,tape,a,d,back);
        park(true);
    }
