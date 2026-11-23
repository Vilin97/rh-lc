module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVan
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.CharpolyNilpotence.IsNilpotentAevalCharpoly
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.NilpotentPowers.IsNilpotentPowSub
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FiberLocalization.EqZeroOfFiberEquivariant
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.DistrC
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.ContinuousCj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.ExistsQuotientHomeo
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsUnimodOfEquiv
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Pieces
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.SemisimpleAdjoint.IsSemisimpleOfMem
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.T2SpaceCentralizerGroup
import GroundTheory.AutomorphicForms.GLnLocal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.RelIndexLatConj
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Unimodularity.UnimodOfIndexSym
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.FrobProof

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.ExistsConjEqSemisimple

section

@[expose] public section

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

section Hyp

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {F : Set (Matrix (Fin n) (Fin n) k)} {P : k[X]}
  {s : Matrix (Fin n) (Fin n) k}
  (hFinv : ∀ g ∈ Gz Z, ∀ x ∈ F, g.val * x * g⁻¹.val ∈ F)
  (hP : ∀ x ∈ F, aeval x P ∈ F ∧ Module.End.IsSemisimple (Matrix.toLin' (aeval x P)) ∧ IsNilpotent (x - aeval x P) ∧
    ∃ g ∈ Gz Z, g.val * aeval x P * g⁻¹.val = s)

include hP in
theorem P_idem [CharZero k] {x} (hx : x ∈ F) : aeval (aeval x P) P = aeval x P := by
  set y := aeval x P with hydef
  obtain ⟨hyF, hyS, -, -⟩ := hP x hx
  obtain ⟨-, hzS, hzN, -⟩ := hP y hyF
  have e : ∀ M : Matrix (Fin n) (Fin n) k, Matrix.toLinAlgEquiv' M = Matrix.toLin' M := fun M => rfl
  have hc : Commute y (aeval y P) := by
    have := (Commute.all (X : k[X]) P).map (aeval y)
    rwa [aeval_X] at this
  have hc' : Commute (Matrix.toLin' y) (Matrix.toLin' (aeval y P)) := by
    have := hc.map (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _)
    rwa [e, e] at this
  have hS : Module.End.IsSemisimple (Matrix.toLin' (y - aeval y P)) := by
    rw [map_sub]
    exact Module.End.IsSemisimple.sub_of_commute hc' hyS hzS
  have hN : IsNilpotent (Matrix.toLin' (y - aeval y P)) := by
    rw [← e]
    exact hzN.map _
  have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hN hS
  rw [← e, map_eq_zero_iff _ (AlgEquiv.injective _), sub_eq_zero] at h0
  exact h0.symm

include hP in
theorem P_mem_Tset [CharZero k] {x} (hx : x ∈ F) : aeval x P ∈ Tset F P := ⟨(hP x hx).1, P_idem hP hx⟩

include hP in
theorem exists_conj_eq_semisimple {x} (hx : x ∈ Tset F P) : ∃ g ∈ Gz Z, cj g x = s := by
  obtain ⟨hxF, hxP⟩ := hx
  obtain ⟨-, -, -, g, hg, hgs⟩ := hP x hxF
  rw [hxP] at hgs
  exact ⟨g, hg, hgs⟩

theorem continuousSMul_actT : @ContinuousSMul (GzS Z) (Tset F P) (actT hFinv).toSMul _ _ := by
  refine @ContinuousSMul.mk _ _ (actT hFinv).toSMul _ _ ?_
  exact (((Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).matrix_mul
    (continuous_subtype_val.comp continuous_snd)).matrix_mul
    (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst))).subtype_mk _

include hP in
theorem isPretransitive_actT (hsT : s ∈ Tset F P) : @MulAction.IsPretransitive (GzS Z) (Tset F P) (actT hFinv).toSMul := by
  refine @MulAction.IsPretransitive.mk _ _ (actT hFinv).toSMul ?_
  intro x y
  obtain ⟨a, ha, hax⟩ := exists_conj_eq_semisimple hP x.2
  obtain ⟨b, hb, hby⟩ := exists_conj_eq_semisimple hP y.2
  refine ⟨⟨b⁻¹ * a, (GzS Z).mul_mem ((GzS Z).inv_mem hb) ha⟩, Subtype.ext ?_⟩
  show cj (b⁻¹ * a) x.1 = y.1
  simp only [cj] at hax hby ⊢
  simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  calc (b⁻¹ : GL (Fin n) k).val * a.val * x.1 * (a⁻¹.val * b.val)
      = (b⁻¹ : GL (Fin n) k).val * (a.val * x.1 * a⁻¹.val) * b.val := by
        simp only [Matrix.mul_assoc]
    _ = (b⁻¹ : GL (Fin n) k).val * (b.val * y.1 * b⁻¹.val) * b.val := by rw [hax, hby]
    _ = y.1 := by simp [Matrix.mul_assoc]

end Hyp

end PositivityTheory.RgUd.T.Desc.SLF
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.SliceVanOfFrob

section

@[expose] public section

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc
open PositivityTheory.PfBern.Loc (SC restr restr_surjective pullL mulInd)
open PositivityTheory.PfBern.Frob (FrobeniusReciprocity IsUnimod eqv eqvF transl translF Fib fibSmul)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


theorem sliceVan_of_frob' [CharZero k] (hFr : FrobeniusReciprocity) (hU : Unimod (k := k)) : SliceVan (k := k) := by
  intro n Z hZ s hs hss hV F P hFc hFB hFinv hP ξ hsupp hinv f hf
  have hCR : CR (adj Z s) := CRAdj.cr_adj Z hZ s hs hss
  haveI : T2Space k := t2k
  haveI : TotallyDisconnectedSpace k := tdk
  haveI : SecondCountableTopology k := sck
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  rcases F.eq_empty_or_nonempty with hF0 | ⟨x0, hx0⟩
  · exact hsupp f ⟨hf.1, Set.subset_univ _⟩ (fun p hp => by simp [hF0] at hp)
  have hsT : s ∈ Tset F P := by
    obtain ⟨g, hg, e⟩ := exists_conj_eq_semisimple hP (P_mem_Tset hP hx0)
    rw [← e]
    exact cj_mem_Tset hFinv hg (P_mem_Tset hP hx0)

  letI A := actT (P := P) hFinv
  haveI := continuousSMul_actT (P := P) hFinv
  haveI := isPretransitive_actT hFinv hP hsT
  haveI : LocallyCompactSpace (Tset F P) := (isClosed_Tset hFc P).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let t : Tset F P := ⟨s, hsT⟩
  obtain ⟨e, he⟩ := exists_quotient_homeo (G := GzS Z) t
  let H := MulAction.stabilizer (GzS Z) t
  have hHc : IsClosed (H : Set (GzS Z)) := by
    have : (H : Set (GzS Z)) = (fun g : GzS Z => g • t) ⁻¹' {t} := by ext g; rfl
    rw [this]
    exact isClosed_singleton.preimage (continuous_id.smul continuous_const)
  haveI : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have memH : ∀ g : GzS Z, g ∈ H ↔ s * g.1.val = g.1.val * s := by
    intro g
    have h1 : g.1⁻¹.val * g.1.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : g.1.val * g.1⁻¹.val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    show g • t = t ↔ _
    constructor
    · intro h
      have e1 : g.1.val * s * g.1⁻¹.val = s := congrArg Subtype.val h
      calc s * g.1.val = g.1.val * s * g.1⁻¹.val * g.1.val := by rw [e1]
        _ = g.1.val * s := by rw [mul_assoc, h1, mul_one]
    · intro h
      apply Subtype.ext
      change g.1.val * s * g.1⁻¹.val = s
      rw [← h, mul_assoc, h2, mul_one]
  have uG : IsUnimod (GzS Z) := hU n Z hZ
  let φ : H ≃ₜ* GzS (adj Z s) :=
    { toFun := fun h => ⟨h.1.1, mem_Gz_adj_iff.2 ⟨h.1.2, (memH h.1).1 h.2⟩⟩
      invFun := fun g => ⟨⟨g.1, (mem_Gz_adj_iff.1 g.2).1⟩, (memH _).2 (mem_Gz_adj_iff.1 g.2).2⟩
      left_inv := fun h => rfl
      right_inv := fun g => rfl
      map_mul' := fun a b => rfl
      continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _ }
  have uH : IsUnimod H := isUnimod_of_equiv φ (hU n (adj Z s) hCR)

  letI B := actX (F := F) hFinv
  haveI := continuousSMul_actX (F := F) hFinv
  have hXc : IsClosed (Xs F) := hFc.prod isClosed_univ
  haveI : LocallyCompactSpace (Xs F) := hXc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let σX : Xs F → Tset F P := fun q => ⟨aeval q.1.1 P, P_mem_Tset hP q.2.1⟩
  have hσc : Continuous σX :=
    Continuous.subtype_mk ((continuous_aevalM P).comp (continuous_fst.comp continuous_subtype_val)) _
  have hσeq : ∀ (g : GzS Z) (q : Xs F), σX (g • q) = g • σX q := fun g q =>
    Subtype.ext (Asm.aeval_conj g.1 q.1.1 P)
  have he_eq : ∀ (g : GzS Z) (c : GzS Z ⧸ H), e (g • c) = g • e c := by
    intro g c
    induction c using QuotientGroup.induction_on with
    | H g' => rw [MulAction.Quotient.smul_mk, he, he, smul_assoc]
  let p : Xs F → GzS Z ⧸ H := fun q => e.symm (σX q)
  have hpc : Continuous p := e.symm.continuous.comp hσc
  have hp : ∀ (g : GzS Z) (q : Xs F), p (g • q) = g • p q := by
    intro g q
    apply e.injective
    simp only [p, Homeomorph.apply_symm_apply, he_eq, hσeq]
  have hfib : ∀ q : Xs F, p q = ((1 : GzS Z) : GzS Z ⧸ H) ↔ aeval q.1.1 P = s := by
    intro q
    constructor
    · intro h
      have h' : σX q = e ((1 : GzS Z) : GzS Z ⧸ H) := by rw [← h]; simp [p]
      rw [he, one_smul] at h'
      exact congrArg Subtype.val h'
    · intro h
      apply e.injective
      simp only [p, Homeomorph.apply_symm_apply, he, one_smul]
      exact Subtype.ext h

  letI : MeasurableSpace (GzS Z) := borel _
  haveI : BorelSpace (GzS Z) := ⟨rfl⟩
  obtain ⟨Fr, hFr1, -⟩ := hFr (GzS Z) H hHc uG uH (Xs F) p hpc hp (1 : GzS Z →* ℂˣ)
    (by simpa using continuous_const) Measure.haar Measure.haar

  obtain ⟨D, hD⟩ := exists_distr_on ξ hXc hsupp
  let actH : GL (Fin n) k → Sp k n ≃ₜ Sp k n := fun g =>
    { toFun := act g, invFun := act g⁻¹
      left_inv := fun q => by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv := fun q => by rw [← act_mul, mul_inv_cancel, act_one]
      continuous_toFun := continuous_act.comp (continuous_const.prodMk continuous_id)
      continuous_invFun := continuous_act.comp (continuous_const.prodMk continuous_id) }
  have hDeqv : D ∈ eqv (X := Xs F) (1 : GzS Z →* ℂˣ) := by
    intro g φ0
    obtain ⟨f0, rfl⟩ := restr_surjective hXc φ0
    let f1 : SC (Sp k n) := pullL (actH g⁻¹.1) f0
    have e1 : transl g (restr hXc f0) = restr hXc f1 := Subtype.ext (funext fun x => rfl)
    rw [e1]
    simp only [MonoidHom.one_apply, Units.val_one, one_mul]
    exact ((hD f1).symm.trans (hinv g⁻¹.1 (g⁻¹).2 f0 ⟨f0.2, Set.subset_univ _⟩)).trans (hD f0)
  let C : Set (Xs F) := {q | q.1.2 = 0}
  have hCc : IsClosed C := isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
  have hCinv : ∀ (g : GzS Z), ∀ x ∈ C, g • x ∈ C := by
    intro g x hx
    change g.1.val *ᵥ x.1.2 = 0
    rw [show x.1.2 = 0 from hx, Matrix.mulVec_zero]
  have hSD : PositivityTheory.PfBern.Frob.SupportedIn (D : PositivityTheory.PfBern.Frob.Distr (Xs F)) C := by
    refine (hFr1 ⟨D, hDeqv⟩ C hCc hCinv).2 ?_
    intro φ0 hφ0
    have hEeqv := (Fr ⟨D, hDeqv⟩).2
    set E : PositivityTheory.PfBern.Frob.Distr (Fib p) := ((Fr ⟨D, hDeqv⟩ : eqvF hp _) : PositivityTheory.PfBern.Frob.Distr (Fib p)) with hEdef
    let Ys : Set (Sp k n) := {q | q.1 ∈ F ∧ aeval q.1 P = s}
    have hYc : IsClosed Ys := (hFc.preimage continuous_fst).inter
      (isClosed_eq ((continuous_aevalM P).comp continuous_fst) continuous_const)
    let hY : Fib p ≃ₜ Ys :=
      { toFun := fun z => ⟨z.1.1, z.1.2.1, (hfib z.1).1 z.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1, trivial⟩, (hfib _).2 y.2.2⟩
        left_inv := fun z => rfl
        right_inv := fun y => rfl
        continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
        continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _ }
    let E' : PositivityTheory.PfBern.Loc.Distr Ys := E.comp (pullL hY)
    obtain ⟨η, hη⟩ := exists_functional hYc E'
    have hcommY : ∀ y ∈ Ys, s * y.1 = y.1 * s := by
      intro y hy
      have := Asm.comm_aeval (a := y.1) (x := y.1) rfl P
      rw [hy.2] at this
      exact this.symm
    have hSη : Supp η (Bz (adj Z s) ×ˢ Set.univ) := by
      intro f hf1 hvan
      have hr : restr hYc ⟨f, hf1.1⟩ = 0 := Subtype.ext (funext fun y =>
        hvan y.1 ⟨mem_Bz_adj (hFB y.2.1) (hcommY y.1 y.2), trivial⟩)
      have := hη ⟨f, hf1.1⟩
      rw [hr, map_zero] at this
      exact this
    have hIη : Inv (adj Z s) η := by
      intro h hh f hf1
      obtain ⟨hhZ, hhs⟩ := mem_Gz_adj_iff.1 hh
      let hG : GzS Z := ⟨h, hhZ⟩
      let hH : H := ⟨hG, (memH hG).2 hhs⟩
      let f1 : SC (Sp k n) := pullL (actH h) ⟨f, hf1.1⟩
      have key : pullL hY (restr hYc f1) = translF hp hH⁻¹ (pullL hY (restr hYc ⟨f, hf1.1⟩)) :=
        Subtype.ext (funext fun z => rfl)
      have h1 : η (fun q => f (act h q)) = η f1 := rfl
      rw [h1, hη f1, hη ⟨f, hf1.1⟩]
      change E (pullL hY (restr hYc f1)) = E (pullL hY (restr hYc ⟨f, hf1.1⟩))
      rw [key]
      exact (hEeqv hH⁻¹ _).trans (by simp)
    have hkill := hV η hSη hIη
    let φ' : SC Ys := pullL hY.symm φ0
    obtain ⟨f0, hf0⟩ := restr_surjective hYc φ'
    have hsupp' : Function.support (φ' : Ys → ℂ) ⊆ {y | y.1.2 ≠ 0} := fun y hy => hφ0 hy
    have hK : IsCompact (Subtype.val '' Function.support (φ' : Ys → ℂ)) :=
      (isCompact_support φ'.2).image continuous_subtype_val
    have hKsub : Subtype.val '' Function.support (φ' : Ys → ℂ) ⊆ {q : Sp k n | q.2 ≠ 0} := by
      rintro _ ⟨y, hy, rfl⟩
      exact hsupp' hy
    have hUo : IsOpen {q : Sp k n | q.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
    obtain ⟨Bc, hBc, hBo, hKB, hBU⟩ := exists_isCompact_isOpen_between hK hUo hKsub
    let f : SC (Sp k n) := mulInd Bc ⟨hBc.isClosed, hBo⟩ f0
    have hrf : restr hYc f = φ' := by
      apply Subtype.ext
      funext y
      change Bc.indicator 1 y.1 * (f0 : Sp k n → ℂ) y.1 = (φ' : Ys → ℂ) y
      have e0 : (f0 : Sp k n → ℂ) y.1 = (φ' : Ys → ℂ) y := congrFun (congrArg Subtype.val hf0) y
      by_cases hyB : y.1 ∈ Bc
      · simp [hyB, e0]
      · have : (φ' : Ys → ℂ) y = 0 := by
          by_contra hne
          exact hyB (hKB ⟨y, hne, rfl⟩)
        simp [hyB, this]
    have hfU : (f : Sp k n → ℂ) ∈ supportedIn {q : Sp k n | q.2 ≠ 0} := by
      refine ⟨f.2, fun q hq => hBU ?_⟩
      by_contra hqB
      exact hq (by simp [f, mulInd, hqB])
    have hz := hkill f hfU
    rw [hη f, hrf] at hz
    have e2 : pullL hY φ' = φ0 := PositivityTheory.PfBern.Loc.pullL_pullL_symm hY φ0
    change E (pullL hY φ') = 0 at hz
    rw [e2] at hz
    exact hz

  rw [show ξ f = D (restr hXc ⟨f, hf.1⟩) from hD ⟨f, hf.1⟩]
  refine hSD _ fun x hx hxC => hx ?_
  have h0 : x.1.2 = 0 := hxC
  show f x.1 = 0
  by_contra hfx
  exact hf.2 hfx h0

end PositivityTheory.RgUd.T.Desc.SLF
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Unimodularity.Imports

section

@[expose] public section

namespace PositivityTheory.RgUd.T.Desc.SLF.Un2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unimod [CharZero k] : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) :=
  unimod_of_indexSym PositivityTheory.RgUd.T.Desc.SLT.indexSym

end PositivityTheory.RgUd.T.Desc.SLF.Un2
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.DescFinal

section

@[expose] public section

namespace PositivityTheory.RgUd.T.Desc.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sliceVan [CharZero k] : SliceVan (k := k) :=
  SLF.sliceVan_of_frob' PositivityTheory.PfBern.Frob.frobeniusReciprocity SLF.Un2.unimod

theorem descA [CharZero k] : DescA (k := k) := Asm.descA_of JC.jcPoly (sliceVan k)

end PositivityTheory.RgUd.T.Desc.Final
end
end
