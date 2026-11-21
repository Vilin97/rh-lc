module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetupLGood
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnivL
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.EtaPiece

@[expose] public section

local macro "kc%" t:term:max : term => `(by with_unfolding_all exact ($t :))

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))

section
open GlobalTheory.ExportSeries
variable {S U : Formalism.BasicNotions.TH.HSp (Dof x)}

private theorem placeMapL_eq (F : Frame S U) : (frL L F).placeMap = F.placeMap := by
  funext e
  delta Frame.placeMap
  rewrite [placeModel_eq x.o.Z (oL x L).Z]
  with_unfolding_all rfl

private theorem vecAtL_eq (X : ExportSeries.Base S U) : (baseL L X).vecAt = X.vecAt := by
  delta ExportSeries.Base.vecAt Frame.vec
  have h : (baseL L X).F.placeMap = (kc% X.F.placeMap) := kc% (placeMapL_eq L X.F)
  rewrite [h]
  with_unfolding_all rfl
end

open GlobalTheory.SeriesTie in
private theorem setupVecAtL_eq (ρ : Setup (Dof x).ntw) (i : (DL x L).ntw.Tw)
    (j : Fin (DL x L).R.m) (b : Bool) :
    ((setupL L ρ).B i j b).vecAt = (kc% ((ρ.B (kc% i) (kc% j) b).vecAt)) :=
  kc% (vecAtL_eq L (ρ.B (kc% i) (kc% j) b))

open GlobalTheory.SeriesTie in
private theorem gens_eq_pz (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).gens = fun i j b k Q ψ h P => (by exact ρ.gens i j b k Q ψ h P) := by
  funext i j b k Q ψ h P
  delta GlobalTheory.SeriesTie.Setup.gens GlobalTheory.ExportSeries.Base.genSet GlobalTheory.ExportSeries.Base.gen GlobalTheory.ExportSeries.Base.vecFlat
  with_unfolding_all
    rewrite [setupVecAtL_eq L ρ i j b]
    rfl
open GlobalTheory.SeriesTie in
private theorem sum_eq_pz (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).sum = fun i j b k Q ψ => (by exact ρ.sum i j b k Q ψ) := by
  funext i j b k Q ψ
  let t := ρ.tw (kc% i) b k (kc% Q) (kc% ψ)
  have h := SerCopy.classSum_eq (a := x.o.Z) (oL x L).Z (ρ.B (kc% i) (kc% j) b)
    (ρ.om (kc% i) (kc% j) b t.chi) t (ρ.rep (kc% i) (kc% j) b t)
  with_unfolding_all exact (h :)
open GlobalTheory.SeriesTie in
private theorem xi_eq_pz (ρ : Setup (Dof x).ntw) (i : (DL x L).ntw.Tw) (j : Fin (DL x L).R.m) (b : Bool) :
    (setupL L ρ).xi i j b (DL x L).nexp =
      fun Q M h P a => kc% (ρ.xi (kc% i) (kc% j) b (Dof x).nexp (kc% Q) M (kc% h) (kc% P) (kc% a)) := by
  funext Q M
  let places := admissibleConjugatePairPlaces (Dof x).ntw (kc% i) (kc% Q) M
  let u := univOf (Dof x).nexp (kc% i) places M ρ.rc
  have h := SerCopy.xiCoef_eq (a := x.o.Z) (oL x L).Z (ρ.B (kc% i) (kc% j) b)
    (ρ.om (kc% i) (kc% j) b 1) u
  have hQ := congrFun h (kc% (half (ρ.ch (kc% i)) places))
  with_unfolding_all exact
    (congrFun hQ (kc% (GlobalTheory.ExportSeries.Base.univFam u (ρ.β (kc% j)))) :)
open GlobalTheory.SeriesTie in
private theorem isHeckeDatum_eq_pz (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).IsHeckeDatum =
      fun i j b k P α R z => (by exact ρ.IsHeckeDatum i j b k P α R z) := by
  funext i j b k P α R z
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · exact (by with_unfolding_all exact ((⟨(d.elt), (d.reps), (d.det)⟩ : ρ.IsHeckeDatum ((i)) ((j)) b k ((P)) ((α)) ((R)) ((z))) : _))
  · exact ⟨(by with_unfolding_all exact (d.elt :)), (by with_unfolding_all exact (d.reps :)), (by with_unfolding_all exact (d.det :))⟩
section Cell
open GlobalTheory.SeriesTie
variable {ρ : Setup (Dof x).ntw} {i : (DL x L).ntw.Tw} {j : Fin (DL x L).R.m} {c : Bool}
private def rdL_pz (rd : Rd ρ (Dof x).nexp ((i)) ((j)) c) : Rd (setupL L ρ) (DL x L).nexp i j c := (rd)
private theorem rat_iff_pz (hρ : ρ.Good) (rd : Rd ρ (Dof x).nexp ((i)) ((j)) c) :
    SeriesTie.Rat (setupL_good L hρ) (@rdL_pz K B f T w P x L ρ i j c rd) ↔ SeriesTie.Rat hρ rd := by
  conv_lhs => delta SeriesTie.Rat RatBase RatTwist RatUniv
  rewrite [isDatum_eq L ρ, theta_eq L ρ, gens_eq_pz L ρ, xi_eq_pz L ρ i j c]
  with_unfolding_all exact (Iff.rfl : SeriesTie.Rat hρ rd ↔ SeriesTie.Rat hρ rd)
private theorem heckeTie_imp_pz {rd : Rd ρ (Dof x).nexp ((i)) ((j)) c} (h : HeckeTie rd) :
    HeckeTie (@rdL_pz K B f T w P x L ρ i j c rd) := by
  delta HeckeTie HeckeAt
  rewrite [isHeckeDatum_eq_pz L ρ]
  exact (by with_unfolding_all exact (h :))
private def cellL_pz {hρ : ρ.Good} {rd : Rd ρ (Dof x).nexp ((i)) ((j)) c} (t : CellTie hρ (Dof x).nexp rd) :
    CellTie (setupL_good L hρ) (DL x L).nexp (i := i) (j := j) (b := c) (@rdL_pz K B f T w P x L ρ i j c rd) where
  supp := (by with_unfolding_all exact (t.supp :))
  cls := (by with_unfolding_all exact (t.cls :))
  coef := (by with_unfolding_all exact (t.coef :))
  rdV := (by with_unfolding_all exact (t.rdV :))
  U_eq := (by with_unfolding_all exact (t.U_eq :))
  psiU_eq := (by with_unfolding_all exact (t.psiU_eq :))
  dat := by rewrite [isDatum_eq L ρ]; exact (by with_unfolding_all exact (t.dat :))
  dat_onto := by rewrite [isDatum_eq L ρ, theta_eq L ρ]; exact (by with_unfolding_all exact (t.dat_onto :))
  lev_iff := (by with_unfolding_all exact (t.lev_iff :))
  th_eq := by rewrite [theta_eq L ρ]; exact (by with_unfolding_all exact (t.th_eq :))
  thPsi_iff := by rewrite [gens_eq_pz L ρ]; exact (by with_unfolding_all exact (t.thPsi_iff :))
  thU_eq := by
    intro Q M d hQ coeffs hcoeffs
    rewrite [xi_eq_pz L ρ i j c] at hcoeffs
    with_unfolding_all exact t.thU_eq Q M d hQ coeffs hcoeffs
  thU_off := by
    intro Q M d hOff
    rewrite [xi_eq_pz L ρ i j c] at hOff
    with_unfolding_all exact t.thU_off Q M d hOff
  rdV_inj := (by with_unfolding_all exact (t.rdV_inj :))
  mtLat_iff := kc% t.mtLat_iff
  thP_eq := by rewrite [sum_eq_pz L ρ]; exact (by with_unfolding_all exact (t.thP_eq :))
private theorem isNormL_pz (ρ : Setup (Dof x).ntw) (i : (DL x L).ntw.Tw) (j : Fin (DL x L).R.m) (c : Bool) (ν : ℂ) :
    IsNorm (datL x L).R (datL x L).geo.v₀ ((setupL L ρ).B i j c) ν ↔
      IsNorm x.m.z.R x.m.z.geo.v₀ (ρ.B ((i)) ((j)) c) ν := by
  conv_lhs => delta IsNorm IsScale
  with_unfolding_all
    rewrite [famTie_eq x.o.Z (oL x L).Z]
    rfl
end Cell
section Comparison₂
open GlobalTheory.SeriesTie
variable (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x)
theorem rat_setupL_iff_rat_realRd {ρ : Setup (Dof x).ntw} (h : ρ.Good) (i : (DL x L).ntw.Tw) (j : Fin (DL x L).R.m) (c : Bool) (ν : ℂ) :
    SeriesTie.Rat (setupL_good L h) (realRd (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (setupL_good L h) i j c ν) ↔
      SeriesTie.Rat h (realRd l.b.YS x.m.z.geo.v₀ h ((i)) ((j)) c ν) :=
  (by with_unfolding_all exact ((@rat_iff_pz K B f T w P x L ρ i j c h (((realRd l.b.YS x.m.z.geo.v₀ h (kc% i) (kc% j) c ν)))) : _))
theorem is_scalar_local_y_structure_of_is_scalar {ρ : Setup (Dof x).ntw} {h : ρ.Good} {i : (DL x L).ntw.Tw} {j : Fin (DL x L).R.m} {c : Bool} {ν : ℂ}
    (s : IsScalar l.b.YS x.m.z.geo.v₀ h ((i)) ((j)) c ν) :
    IsScalar (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (setupL_good L h) i j c ν :=
  ⟨s.ne, fun ⟨ν', h'⟩ => (isNormL_pz L ρ i j c ν).2 (s.norm ⟨ν', (isNormL_pz L ρ i j c ν').1 h'⟩),
    fun ⟨ν', h₁, h₂⟩ => (_root_.GlobalTheory.HeightCounting.Fin3.rat_setupL_iff_rat_realRd L l h i j c ν).2 (s.rat ⟨ν', (isNormL_pz L ρ i j c ν').1 h₁, (_root_.GlobalTheory.HeightCounting.Fin3.rat_setupL_iff_rat_realRd L l h i j c ν').1 h₂⟩)⟩
@[no_expose] def localYStructureExportTie : ExportTie (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ where
  ρ := setupL L l.b.ser.ex.ρ
  good := setupL_good L l.b.ser.ex.good
  pin := _root_.GlobalTheory.HeightCounting.Fin3.real_pin_setup_local L l
  vec := (by with_unfolding_all exact (l.b.ser.ex.vec :))
  ν := (by with_unfolding_all exact (l.b.ser.ex.ν :))
  scalar := fun i j c => _root_.GlobalTheory.HeightCounting.Fin3.is_scalar_local_y_structure_of_is_scalar L l (h := l.b.ser.ex.good) ((by with_unfolding_all exact ((l.b.ser.ex.scalar ((i)) ((j)) c) : _)))
  tie := fun i j c => (by with_unfolding_all exact ((@cellL_pz K B f T w P x L l.b.ser.ex.ρ i j c l.b.ser.ex.good
    (((l.b.ser.ex.rd (kc% i) (kc% j) c))) (((l.b.ser.ex.tie (kc% i) (kc% j) c)))) : _))
  hecke := fun i j c => (by with_unfolding_all exact ((@heckeTie_imp_pz K B f T w P x L l.b.ser.ex.ρ i j c
    (((l.b.ser.ex.rd (kc% i) (kc% j) c))) (((l.b.ser.ex.hecke (kc% i) (kc% j) c)))) : _))
  univ := _root_.GlobalTheory.HeightCounting.Fin3.is_univ_char_local L l
private def lamL_pz (Z : GlobalTheory.LamTie.LamDat (Dof x)) : GlobalTheory.LamTie.LamDat (DL x L) :=
  ⟨(by with_unfolding_all exact ((chFr (a := x.o.Z) (oL x L).Z ((Z.C))) : _)), (by with_unfolding_all exact (Z.q0 :)), (by with_unfolding_all exact (Z.w0 :)), (by with_unfolding_all exact (Z.c :)), (by with_unfolding_all exact (Z.chi :))⟩
private theorem lamL_ok_pz {Z : GlobalTheory.LamTie.LamDat (Dof x)} (h : Z.Ok) : (lamL_pz L Z).Ok := ⟨(by with_unfolding_all exact (h.places :)), (by with_unfolding_all exact (h.aux :)), (by with_unfolding_all exact (h.big :))⟩
private theorem lamL_tie_pz {Z : GlobalTheory.LamTie.LamDat (Dof x)} (h : GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z) :
    GlobalTheory.LamTie.IsLamTieFull (DL x L).ntw (lamL_pz L Z) := (by with_unfolding_all exact (h :))
private theorem lamL_C_pz {Z : GlobalTheory.LamTie.LamDat (Dof x)} (h : Z.C = cfOf x) : (lamL_pz L Z).C = cfD x L :=
  (by with_unfolding_all exact ((congrArg (fun c : CharFrame (Dof x) => chFr (a := x.o.Z) (oL x L).Z ((c))) h) : _))
@[no_expose] def seriesAtLocal (X : Formalism.L2.NExpTied (withLoc L)) (h : ExpRel L l.b.Bs.exp X) :
    SerAt (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (expD L X) (_root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l) (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.placeMapLocal L l) where
  ex := _root_.GlobalTheory.HeightCounting.Fin3.localYStructureExportTie L l
  bad := (by with_unfolding_all exact (l.b.ser.bad :))
  ch := (by with_unfolding_all exact (l.b.ser.ch :))
  join := fun i j b k Q ψ hA ht => (by with_unfolding_all exact ((h.reads (kc% i) (j.1 + 1) b k (kc% Q) (kc% ψ) (Nat.le_add_left _ _) (kc% j.2) (kc% hA)
    (l.b.ser.ex.ρ.ek (kc% i) b k)
    (Formalism.IndefR.Links.PolF (Dof x) (Formalism.IndefR.Links.Wc (Dof x) (kc% j)).rank (Formalism.IndefR.Links.Vc (Dof x) (kc% j)).rank)
    (fun f g => (l.b.ser.ex.tie (kc% i) (kc% j) b).rdV k (kc% Q) (kc% ψ) (kc% f)
      ((Formalism.L2.Theta.finHom _).rangeRestrict ((l.mt.ad.PV (kc% j)).ψ (kc% g))))
    (kc% (l.b.ser.join (kc% i) (kc% j) b k (kc% Q) (kc% ψ) (kc% hA) (kc% ht)))) :))
  sup := kc% l.b.ser.sup
  off := (by with_unfolding_all exact (l.b.ser.off :))
  lam := lamL_pz L l.b.ser.lam
  lam_ok := lamL_ok_pz L l.b.ser.lam_ok
  lam_teich := (by with_unfolding_all exact (l.b.ser.lam_teich :))
  lam_C := lamL_C_pz L l.b.ser.lam_C
  lam_q := (by with_unfolding_all exact (l.b.ser.lam_q :))
  lam_tie := lamL_tie_pz L l.b.ser.lam_tie
end Comparison₂
end GlobalTheory.HeightCounting.Fin3
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.series_at_local_of_exp_relation : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (X : Formalism.L2.NExpTied (withLoc L)), ExpRel L l.b.Bs.exp X → Nonempty (SerAt (_root_.GlobalTheory.HeightCounting.Fin3.yStructureLocal L l) (datL x L).geo.v₀ (expD L X) (_root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l) (cfD x L) (_root_.GlobalTheory.HeightCounting.Fin3.placeMapLocal L l)) :=
  fun L l X h => ⟨_root_.GlobalTheory.HeightCounting.Fin3.seriesAtLocal L l X h⟩
end
