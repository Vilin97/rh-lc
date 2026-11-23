module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OverIx
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MapSeqIndAll
public import Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoTiedPGraft
public import Formalism.LocalRingCardinality.SpanPowerMembership.UnitsPowSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertAtLeCongN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTwistOfIsDelta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationLtOneOfInvNotMem
import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoTiedPGraft
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QpIsQpSet

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.QpIsOf

theorem qpIs_qpSet : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), ColPin w → ∀ (Z : w.Lt) {nch : NChoice (w.D Z)}
    (tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch), tp.xi = w.I.xi → GlobalTheory.Mem.HD.TupPins tp →
    TC.QpIs w.I (GlobalTheory.Mem.HD.ReQ.qpSet tp) := by
  intro B f T w _ Z nch tp hxi _ a p
  classical
  have hr := w.ok.xi_reads a
  have hsel : Formalism.L2.Col.IsSel B.fields w.I.sel := w.ok.sel_ok
  have hf := GlobalTheory.OpenChrRam.qprime_finite B.fields.F B.fields.E B.fields.K ((w.I.tup a : Formalism.L2.DIV.Chr _ _ _))
    (w.I.tup a).2.1.1.1.1.2
  have hpm : ∀ (v : HeightOneSpectrum (𝓞 B.fields.F)) (P : HeightOneSpectrum (𝓞 B.fields.E)),
      Ideal.under (𝓞 B.fields.F) P.asIdeal = v.asIdeal → ((p : 𝓞 B.fields.E) ∈ P.asIdeal ↔ (p : 𝓞 B.fields.F) ∈ v.asIdeal) := by
    intro v P h
    rw [← h, Ideal.under, Ideal.mem_comap, map_natCast]
  have hx : ∀ P, (tp.xi a).UnrAt P ↔ (w.I.xi a).UnrAt P := fun P => by rw [congrFun hxi a]; exact Iff.rfl
  refine (GlobalTheory.Mem.HD.ReQ.mem_qpSet tp a p).trans ?_
  refine Iff.trans (and_congr_right fun _ => exists_congr fun P => and_congr_right fun _ => not_congr (hx P)) ?_
  show (p.Prime ∧ ∃ P, (p : 𝓞 B.fields.E) ∈ P.asIdeal ∧ ¬ (w.I.xi a).UnrAt P) ↔
    p.Prime ∧ ∃ P ∈ Formalism.L2.Col.QE w.I.sel (w.I.tup a : Formalism.L2.DIV.Chr _ _ _), (p : 𝓞 B.fields.E) ∈ P.asIdeal
  rw [Formalism.L2.Col.QE, dite_eq_left hf]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨P, hp, hP⟩
    refine ⟨w.I.sel (P.under (𝓞 B.fields.F)),
      Finset.mem_image_of_mem _ (hf.mem_toFinset.2 ((GlobalTheory.Mem.ReadTwist.mem_qprime_iff hr _).2 ⟨P, rfl, hP⟩)), ?_⟩
    rw [hpm _ _ (hsel _), ← hpm _ P rfl]
    exact hp
  · rintro ⟨P, hP, hp⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨P', hP', hr'⟩ := (GlobalTheory.Mem.ReadTwist.mem_qprime_iff hr v).1 (hf.mem_toFinset.1 hv)
    refine ⟨P', ?_, hr'⟩
    rw [hpm v P' (by rw [← hP']; rfl), ← hpm v _ (hsel v)]
    exact hp

end GlobalTheory.Mem.Top.Bl.QpIsOf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIs

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD.TupPin

theorem isTwist_types (B : Base) (f : Fr B.toPre) (T : TwDat B) :
    ∀ ξ ∈ T.set f, Chr.IsTwist B.host (Set.range B.host.g) ξ := by
  have a1 : Chr.IsTwist B.host (Set.range B.host.g) f.del := Chr.isTwist_of_isDelta B.host.pde_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde_prime B.pde_cond.1).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).1 h.symm) f.isDel
  have a2 : Chr.IsTwist B.host (Set.range B.host.g) f.del' := Chr.isTwist_of_isDelta B.host.pde'_prime
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ B.host.pde'_prime B.pde_cond.2).1
    (fun ⟨i, h⟩ => (B.host.pde_ne_g i).2 h.symm) f.isDel'
  rintro ξ ((rfl | rfl | rfl) | ⟨w, rfl⟩)
  · exact Chr.isTwist_one _ _
  · exact a1
  · exact a2
  · have h := T.psi_tw w
    have a3 : Chr.IsTwist B.host (Set.range B.host.g) (T.psi w) := ⟨h.1, h.2.1, h.2.2.1, fun v hv =>
      ⟨(h.2.2.2 v hv).1, (h.2.2.2 v hv).2.1, (h.2.2.2 v hv).2.2.1,
        fun ⟨i, hi⟩ => (h.2.2.2 v hv).2.2.2 (Or.inr (Or.inl ⟨i, hi.symm⟩))⟩⟩
    unfold TwDat.xiTw
    split_ifs
    exacts [a2.mul_twist a3, a1.mul_twist a3]

theorem xiTw_unr (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : B.places.Pl) (v : HeightOneSpectrum (𝓞 B.host.E))
    (hv : OverP B.host (B.places.resChar w) v) : (T.xiTw f w).UnrAt v := by
  have hψ : (T.psi w).UnrAt v := fun x _ => (T.psi_is w).atl v hv x
  unfold TwDat.xiTw
  split_ifs with h
  · refine (f.isDel'.unr v fun hn => B.host.pde_ne ?_).mul hψ
    rw [h] at hv
    exact Examples₂.PlacesToy.prime_mem_unique v B.host.pde_prime B.host.pde'_prime hv hn
  · exact (f.isDel.unr v fun hn => h
      (Examples₂.PlacesToy.prime_mem_unique v (B.places.resChar_prime w) B.host.pde_prime hv hn)).mul hψ

end GlobalTheory.Mem.HD.TupPin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToIntBijective

section

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.Rows Formalism.L2.Geo GlobalTheory.GeoGraft NumberField

namespace GlobalTheory.GeoModel

variable (D : D7)

def fracO : IntermediateField ℚ D.what₂.LL := IntermediateField.adjoin ℚ (Set.range D.what₂.OtoLL)

theorem otoLL_mem (y : D.what₂.O) : D.what₂.OtoLL y ∈ fracO D :=
  IntermediateField.subset_adjoin ℚ _ ⟨y, rfl⟩

variable {D} {T : HostTied D} {C : CharFrame D}

def toInt (h : OTied D T C) : D.what₂.O →+* 𝓞 (fracO D) where
  toFun y := ⟨⟨D.what₂.OtoLL y, otoLL_mem D y⟩, by
    have hq : IsIntegral ℤ (T.jLL (D.what₂.OtoLL y)) := ((h.range _).1 ⟨y, rfl⟩).2
    let f : (fracO D) →ₐ[ℤ] Qb := (T.jLL.comp (fracO D).val.toRingHom).toIntAlgHom
    have hf : Function.Injective f := (T.jLL.comp (fracO D).val.toRingHom).injective
    exact (isIntegral_algHom_iff f hf).1 hq⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; exact map_mul D.what₂.OtoLL a b
  map_zero' := by ext; simp
  map_add' a b := by ext; exact map_add D.what₂.OtoLL a b

theorem toInt_val (h : OTied D T C) (y : D.what₂.O) : ((toInt h y : fracO D) : D.what₂.LL) = D.what₂.OtoLL y := rfl

theorem toInt_bijective (h : OTied D T C) : Function.Bijective (toInt h) := by
  refine ⟨fun a b hab => h.inj ?_, fun z => ?_⟩
  · have := congrArg (fun w : 𝓞 (fracO D) => ((w : fracO D) : D.what₂.LL)) hab
    simpa [toInt_val] using this
  · set x : D.what₂.LL := ((z : fracO D) : D.what₂.LL) with hx
    have hint : IsIntegral ℤ (T.jLL x) := by
      let f : (fracO D) →ₐ[ℤ] Qb := (T.jLL.comp (fracO D).val.toRingHom).toIntAlgHom
      have hf : Function.Injective f := (T.jLL.comp (fracO D).val.toRingHom).injective
      exact (isIntegral_algHom_iff f hf).2 z.2
    have hmem : T.jLL x ∈ KsQ D T C h.pieces := by
      have hx' : x ∈ fracO D := (z : fracO D).2
      have h1 : T.jLL x ∈ (fracO D).map T.jLL.toRatAlgHom := ⟨x, hx', rfl⟩
      rw [fracO, IntermediateField.adjoin_map] at h1
      refine (IntermediateField.adjoin_le_iff.2 ?_) h1
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ((h.range _).1 ⟨y, rfl⟩).1
    obtain ⟨y, hy⟩ := (h.range _).2 ⟨hmem, hint⟩
    refine ⟨y, ?_⟩
    ext
    exact T.jLL.injective hy

def eO (h : OTied D T C) : 𝓞 (fracO D) ≃+* D.what₂.O := (RingEquiv.ofBijective _ (toInt_bijective h)).symm

end GlobalTheory.GeoModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.DivRec

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem nonempty_ix (hH : Holds R F) : Nonempty A3.fam3.base3.Ix :=
  GlobalTheory.Div.nonempty_ix_of_pos A3 F.P0 F.ψ0 (R.toCx3 F).zs hH.ok hH.prim.block (hH.prim.pos false)


open Classical in
def labOf (Z : ReadL R F X0 Y) (hH : Holds R F) (σ : D.what₂.FT) : A3.fam3.base3.Ix :=
  if h : ∃ c, Bl.OverIx Z σ c then h.choose else (nonempty_ix hH).some

theorem overIx_labOf (Z : ReadL R F X0 Y) (hH : Holds R F) (σ : D.what₂.FT) (h : ∃ c, Bl.OverIx Z σ c) :
    Bl.OverIx Z σ (labOf Z hH σ) := by
  rw [labOf, dite_eq_left h]
  exact h.choose_spec


open Classical in
def logLamOf (Z : ReadL R F X0 Y) (hH : Holds R F) (j : ℕ) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ) : ℝ :=
  if e = D.what₂.embLL then Real.log (D.what₂.lamP D.what₂.mu0 j σ)
  else if h : j - 1 < D.R.m then
    if D.what₂.isot j σ = ⊥ then 0 else Real.log ((s0Of R F).lam ⟨j - 1, h⟩ A3.A.μ0 (labOf Z hH σ) (InfinitePlace.mk e))
  else 0

theorem lamAre_of_eq (Z : ReadL R F X0 Y) (hH : Holds R F) (Xd : DivX D) (hX : Xd.logLam = logLamOf Z hH) : Bl.LamAre Z Xd := by
  refine ⟨labOf Z hH, overIx_labOf Z hH, fun i σ e he => ?_⟩
  have h : (i : ℕ) + 1 - 1 < D.R.m := i.2
  rw [hX, logLamOf, if_neg he, dite_eq_left h]
  exact ⟨fun h0 => if_neg h0, fun h0 => if_pos h0⟩

def x0 (Z : ReadL R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) : DivX D where
  geo := Formalism.BasicNotions.Examples₂.geoExample _
  Lev := Empty
  levPr := fun κ => κ.elim
  shv := fun _ κ => κ.elim
  shv_N := fun _ κ => κ.elim
  shv_lev := fun _ κ => κ.elim
  PlP := fun p _ => Formalism.L2.Geo.PlL D p
  plpFin := fun p _ => Formalism.L2.Geo.finPl D p
  plpNe := fun p _ => Formalism.L2.Geo.plL_ne D p
  wtP := fun p _ => Formalism.L2.Geo.wtL D p
  divisorWeight_nonneg := fun p _ => Formalism.L2.Geo.wtL_nonneg D p
  divisorWeight_sum := fun p _ => Formalism.L2.Geo.wtL_sum D p
  plP := fun p _ => Formalism.BasicNotions.Examples₂.PlOver.plLEquiv D p
  divisorWeight_def := fun p _ la => Formalism.BasicNotions.Examples₂.PlOver.wtLog_eq D p la
  jC := fun p _ _ => (Formalism.BasicNotions.Examples₂.teich_Om_equiv p).some.toRingHom.comp (algebraMap (DV.KW p) (Formalism.BasicNotions.Examples₂.TeichOm p))
  Mp := fun _ κ => κ.elim
  md := fun _ κ => κ.elim
  vdd := fun _ _ => 0
  vdd_unram := fun _ _ _ => rfl
  phiFr_unram := fun _ κ => κ.elim
  vdd_nonneg := fun _ _ => le_rfl
  CurveM := fun _ κ => κ.elim
  degM := fun _ κ => κ.elim
  htMdl := fun _ κ => κ.elim
  htCurve := fun _ κ => κ.elim
  htCurve_deg := fun _ κ => κ.elim
  MjH := mjH Z
  MjH_good := mjH_good Z hH
  jM := jM Z
  jM_basis := jM_basis Z hH
  jM_lat := jM_lat Z hP hH
  MjLat_sub := mjLat_sub Z hP hH
  jM_metric := jM_metric Z hH
  Qp := fun _ => ∅
  degreeZero_partial_set_empty := rfl
  Qp_muAt := fun _ => Finset.notMem_empty _
  Qp_g := fun _ _ _ => Finset.notMem_empty _
  QPl := fun _ => Empty
  qv := fun _ v => v.elim
  qv_gt := fun _ v => v.elim
  qv_char := fun _ _ v => v.elim
  nu := fun _ v => v.elim
  nu_ne := fun _ v => v.elim
  nu_abs := fun _ v => v.elim
  ZQ := fun _ v => v.elim
  quotientLocalValueFirst := fun _ v => v.elim
  typeDim := fun _ v => v.elim
  Comp := fun _ => Empty
  degHH := fun _ c => c.elim
  Yv := fun _ c => c.elim
  Ybd := fun _ c => c.elim
  Lw := fun _ c => c.elim
  iMj := fun _ c => c.elim
  iMj_mem := fun _ c => c.elim
  logLam := logLamOf Z hH
  logLam_base := fun _ _ => if_pos rfl
  kapR := fun _ => kapSharp D
  kapR_pos := fun _ => RowSide.kapOf_pos _ _
  kapR_conj := fun _ => rfl
  Surf := Empty
  surfCh2 := fun _ => 0
  surfDegOm := fun _ => 0
  SurfFp := Empty
  surfFpCh2 := fun _ => 0

end GlobalTheory.Mem.Top.DivRec

end

noncomputable section

namespace GlobalTheory.Mem.Top.DivRec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tupPins_of_muIsW (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl)
    (xi : X.C.Tup → HChar X.B.host.E) (h : V4.MuIsW X f T Wt xi) {C : CharFrame X.toD7} {nch : NChoice X.toD7}
    (tp : TupTied X.toD7 C nch) (hxi : tp.xi = xi) : GlobalTheory.Mem.HD.TupPins tp := by
  refine ⟨fun μ v hv => ?_, fun w v hv => ?_⟩
  · rw [hxi] at hv
    obtain ⟨h1, h2, h3, h4⟩ :=
      (GlobalTheory.Mem.HD.TupPin.isTwist_types X.B f T (xi μ) (h.range ▸ Set.mem_range_self μ)).2.2.2 v hv
    exact ⟨h1, h2, h3, fun k hk => h4
      ⟨k, Examples₂.PlacesToy.prime_mem_unique v (X.B.host.g_prime k) h2 hk (Ideal.absNorm_mem _)⟩⟩
  · rw [hxi]
    show (xi (X.W.muAt w)).UnrAt v
    by_cases hw : w ∈ Wt
    · rw [h.on w hw, h.tw w]
      exact GlobalTheory.Mem.HD.TupPin.xiTw_unr X.B f T w v hv
    · rw [h.off w hw, h.mu0]
      exact fun _ _ => rfl


open Formalism.L2.Rows Formalism.L2.Geo GlobalTheory.GeoGraft GlobalTheory.GeoModel in
theorem geoOver_stages (X : Stages) (X₀ : DivX X.toD7) : GeoOver (fun _ => True) X₀ := by
  let D := X.toD7
  let eO : 𝓞 X.B.Ks ≃+* D.what₂.O := RingEquiv.refl _
  let kL : X.B.Ks →+* D.what₂.LL := X.B.Ks.val.toRingHom
  have hk : ∀ x : 𝓞 X.B.Ks, kL (x : X.B.Ks) = D.what₂.OtoLL (eO x) := fun _ => rfl
  let jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ) :=
    fun p _ la => Classical.choose (GlobalTheory.WittFracPlace.exists_jcPin D p la)
  have hjc : ComplexEmbeddingsCompatible jc := GlobalTheory.ShFam.PinPlace.pinned_tiedFor D jc
    (fun p _ la => Classical.choose_spec (GlobalTheory.WittFracPlace.exists_jcPin D p la))
  refine ⟨divXFl D jc X₀, fun _ _ => True, ⟨divXFl D jc X₀, (divXFl D jc X₀).iMj, (divXFl D jc X₀).iMj_mem, rfl⟩,
    ⟨famFlJ D jc X.B.Ks eO kL hk, fun p _ => Equiv.refl _, fun _ _ _ => Equiv.refl _, tiedX_fl D jc X₀, hjc,
      fun _ _ _ _ _ => trivial, isoInv_famFlJ D jc X.B.Ks eO kL hk, levInTie_famFlJ D jc X.B.Ks eO kL hk⟩, trivial⟩

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem qpIs_qpSet (w : ColW B f T) (pin : ColPin w) (Z : w.Lt) {nch : NChoice (w.D Z)}
    (tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch) (hxi : tp.xi = w.I.xi) (hp : GlobalTheory.Mem.HD.TupPins tp) :
    TC.QpIs w.I (GlobalTheory.Mem.HD.ReQ.qpSet tp) := GlobalTheory.Mem.Top.Bl.QpIsOf.qpIs_qpSet w pin Z tp hxi hp

theorem exists_divT {𝒮 : Slots} {K : Ctx} (w : ColW B f T) (pin : ColPin w) (Z : w.Lt) (l : Lv4 𝒮 K w Z) :
    ∃ Y : DivX (w.D Z), Nonempty (DivT l.n Y) ∧ MjAre l.what₂.r.Z Y ∧ (∀ σ, Y.kapR σ = kapSharp (w.D Z)) ∧
      LamAre l.what₂.r.Z Y := by
  have hp : GlobalTheory.Mem.HD.TupPins l.n.tp := tupPins_of_muIsW (w.st Z) f T l.Wt w.I.xi l.what₂.mu l.n.tp l.n.xi
  let X₁ := x0 l.what₂.r.Z l.what₂.r.z.pins l.what₂.r.intersectionNumber_baseChange
  let X₂ := GlobalTheory.Mem.HD.ReQ.reQ l.n.tp hp w.I.sel pin.above X₁
  obtain ⟨X, inK, ⟨Xg, iM, hiM, rfl⟩, hG, -⟩ := geoOver_stages (w.st Z) X₂
  let c := GlobalTheory.Mem.HD.ReQ.reducedDivisorCharacter l.n.tp hp w.I.sel pin.above X₁
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.HD.ReQ.reLoc l.n.tp hp w.I.sel pin.above X₁
  let chr : DivisorCharacterCompatibility (w.D Z) (TC.cf w.I w.l Z) _ l.n.tp (GlobalTheory.GeoGraft.graft Xg X₂ iM hiM) := ⟨c.Qp_iff, c.eQPl, c.qv_eq⟩
  refine ⟨GlobalTheory.GeoGraft.graft Xg X₂ iM hiM,
    ⟨{ Qp := qpIs_qpSet w pin Z l.n.tp l.n.xi hp, chr := chr, loc := ⟨h1, ?_⟩, inK := inK, geo := hG }⟩,
    GlobalTheory.Mem.R3.exists_mjHTie l.what₂.r.Z _ rfl HEq.rfl, fun _ => rfl,
    lamAre_of_eq l.what₂.r.Z l.what₂.r.intersectionNumber_baseChange _ rfl⟩
  exact ⟨h2.qv_eq, h2.deg1, h2.ram, h2.off_g, h2.nu_eq, h2.typeDim_eq, h2.ZQ_eq, h2.quotientLocalValueFirst_eq⟩

theorem lamAre_heq {K : Ctx} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 p0' : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0}
    {t' : RowsT K w Z Wt p0'} (e : p0 = p0') (h : HEq t t') {X : DivX (w.D Z)} (hX : LamAre t'.r.Z X) : LamAre t.r.Z X := by
  subst e
  obtain rfl := eq_of_heq h
  exact hX

theorem divEx_prov (𝒮 : Slots) (hOx : 𝒮.Ox = OX anyGeometry) : DivEx 𝒮 :=
  StepW.of_all fun _ _ _ _ w _ _ hpin Z l =>
    let ⟨Y, h1, h2, h3, h4⟩ := exists_divT w hpin.some Z l
    ⟨Y, h1, h2, h3, fun O t hX hp ht => by
      rw [hOx]
      exact ⟨⟨trivial, lamAre_heq hp ht (hX ▸ h4)⟩⟩⟩

theorem divEx_of_ox : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → ∀ 𝒮 : Slots,
    𝒮.Ox = OX anyGeometry → DivEx 𝒮 :=
  fun _ _ _ 𝒮 hOx => divEx_prov 𝒮 hOx

end GlobalTheory.Mem.Top.DivRec

end
end
end
