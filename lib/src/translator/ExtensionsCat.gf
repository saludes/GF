concrete ExtensionsCat of Extensions = 
    CatCat ** 
  open 
    PhonoCat, MorphoCat, ResCat, CommonRomance, ParadigmsCat, SyntaxCat, Prelude, (G = GrammarCat), (E = ExtraCat) in {

lincat
 VPI = E.VPI ;
----  ListVPI = E.ListVPI ;
  VPS = E.VPS ;
----  ListVPS = E.ListVPS ;
  
lin
  MkVPI = E.MkVPI ;
----  ConjVPI = E.ConjVPI ;
----  ComplVPIVV = E.ComplVPIVV ;

  MkVPS = E.MkVPS ;
----  ConjVPS = E.ConjVPS ;
  PredVPS = E.PredVPS ;

----  BaseVPI = E.BaseVPI ;
----  ConsVPI = E.ConsVPI ;
----  BaseVPS = E.BaseVPS ;
----  ConsVPS = E.ConsVPS ;

----  GenIP = E.GenIP ;
----  GenRP = E.GenRP ;

  PassVPSlash = E.PassVPSlash ;
  PassAgentVPSlash = E.PassAgentVPSlash ;


lin
  GenNP np = 
    let denp = (np.s ! ResCat.genitive).ton in {
      s = \\_,_,_,_ => [] ; 
      sp = \\_,_,_ => denp ;
      s2 = denp ; 
      isNeg = False ;
    } ;

  EmptyRelSlash slash = mkRCl which_RP (lin ClSlash slash) ;

  that_RP = which_RP ;

  but_Subj = {s = "però" ; m = Indic} ; ---- strange to have this as Subj



lin
  CompoundN noun cn = {
    s = \\n => cn.s ! n ++ "de" ++ noun.s ! Sg ;
    g = cn.g
  } ;

    CompoundAP noun adj = {
      s = \\af => adj.s ! Posit ! af ++ "de" ++ noun.s ! Sg  ;
      isPre = False
      } ;

{-  
  GerundN v = {
    s = \\n,c => v.s ! VPresPart ;
    g = Neutr
  } ;
  
  GerundAP v = {
    s = \\agr => v.s ! VPresPart ;
    isPre = True
  } ;
-- }

  PastPartAP v = {
    s = table {
      AF g n => v.s ! VPart g n ;
      _ => v.s ! VPart Masc Sg  ---- the adverb form
      } ;
    isPre = True
  } ;

 --{-
  OrdCompar a = {s = \\c => a.s ! AAdj Compar c } ;
-}

  PositAdVAdj a = {s = a.s ! Posit ! AA} ;

{-
  UseQuantPN q pn = {s = \\c => q.s ! False ! Sg ++ pn.s ! npcase2case c ; a = agrgP3 Sg pn.g} ;

  SlashV2V v ant p vp = insertObjc (\\a => v.c3 ++ ant.s ++ p.s ++
                                           infVP v.typ vp ant.a p.p a)
                                   (predVc v) ;

  SlashVPIV2V v p vpi = insertObjc (\\a => p.s ++ 
                                           v.c3 ++ 
                                           vpi.s ! VVAux ! a)
                                   (predVc v) ;
-}
  ComplVV v a p vp = 
      insertComplement (\\a => prepCase v.c2.c ++ infVP vp a) (predV v) ; ---- a,p

---- TODO: find proper expressions for OSV and OVS in Cat
  PredVPosv np vp = mkCl (lin NP np) (lin VP vp) ;
  PredVPovs np vp = mkCl (lin NP np) (lin VP vp) ;


  CompS s = {s = \\_ => "de" ++ "què" ++ s.s ! Indic ; cop = serCopula} ; ---- de ?

{-
  CompQS qs = {s = \\_ => qs.s ! QIndir} ;
  CompVP ant p vp = {s = \\a => ant.s ++ p.s ++ 
                                infVP VVInf vp ant.a p.p a} ;

  VPSlashVS vs vp = 
    insertObj (\\a => infVP VVInf vp Simul CPos a) (predV vs) **
    {c2 = ""; gapInMiddle = False} ;

  PastPartRS ant pol vps = {
    s = \\agr => vps.ad ++ vps.ptp ++ vps.s2 ! agr ;
    c = npNom
    } ;

  PresPartRS ant pol vp = {
    s = \\agr => vp.ad ++ vp.prp ++ vp.s2 ! agr ;
    c = npNom
  } ;

  ApposNP np1 np2 = {
    s = \\c => np1.s ! c ++ "," ++ np2.s ! npNom ;
    a = np1.a
  } ;
  
  AdAdV = cc2 ;
  
  UttAdV adv = adv;
-}

    
}
