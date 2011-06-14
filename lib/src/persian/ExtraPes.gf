concrete ExtraPes of ExtraPesAbs = CatPes ** 
  open ResPes, Coordination, Prelude, MorphoPes, ParadigmsPes in {

  flags coding = utf8;

  lin
    GenNP np = {s = \\_,_,_ => np.s ! NPC Obl ++ "ka" ; a = np.a} ;

    each_Det = mkDet  "hr kwy" "hr kwy" "hr kwy" "hr kwy" Sg ;
    have_V = mkV "rakh-na";
    IAdvAdv adv = {s = "ktny" ++ adv.s} ;
    ICompAP ap = {s = "ktnE" ++ ap.s ! Sg ! Masc ! Dir ! Posit} ;
    cost_V = mkV "qymt" ;
    
    -- added for causitives
    make_CV = mkVerb "nothing"   ** {c2 = "" };

-- for VP conjunction
} 