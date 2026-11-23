module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasCompactSupportDescend
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Algebra.ProperAction.Basic
public import Development.DiscreteGroups.GlobalIrreducibility.LConvSepR
public import Development.DiscreteGroups.GlobalIrreducibility.LConvSepW
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.DiscreteGroups.GlobalIrreducibility.LConvSepA
public import Development.DiscreteGroups.GlobalIrreducibility.LConvSepB

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarIsMulRightInvariant

section

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology Matrix
open scoped ENNReal

namespace GlobalTheory.SmGL.UnipHaar

section Algebra

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)

theorem det_rmat_unip (u : unipRad R e) : (rmat e ((u : GL n R) : Matrix n n R)).det = 1 := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 u.2
  rw [← det_transpose, det_of_blocks (rmat e _)ᵀ (fun p => blk e p.1.2) ?_
    (fun a => {j : n // blk e j < a}) (fun _ => 1) (colEquiv e) ?_]
  · simp
  · intro p q h
    have h3 : ((u : GL n R) : Matrix n n R).BlockTriangular (blk e) := h1
    simp [rmat, h3 h]
  · intro a x y
    exact if_congr (eq_comm.trans Subtype.ext_iff.symm) (h2 a x.1 y.1) rfl

theorem unipEquiv_mul_right (u : unipRad R e) (x : Idx e → R) :
    unipEquiv e ((unipEquiv e).symm x * u) =
      unipEquiv e u + (rmat e ((u : GL n R) : Matrix n n R)).mulVec x := by
  rw [← ent_mat_mul]
  show ent e ((1 + mat e x) * ((u : GL n R) : Matrix n n R)) = _
  rw [add_mul, one_mul]
  rfl

end Algebra

section Measure

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem isMulRightInvariant_map :
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν)).IsMulRightInvariant := by
  haveI := secondCountable k
  haveI := t2Space k
  have hΦ : Measurable (unipHomeo (R := k) e).symm := (unipHomeo e).symm.measurable
  refine ⟨fun u => ?_⟩
  have hm : Measurable (rmat e ((u : GL n k) : Matrix n n k)).mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have h1 := WeilM.smul_map_mulVec_pi ν _ 1 (det_rmat_unip e u).symm
  rw [map_one, ENNReal.coe_one, one_smul] at h1
  have h2 : (· * u) ∘ (unipHomeo e).symm = (unipHomeo e).symm ∘ ((unipEquiv e u + ·) ∘
      (rmat e ((u : GL n k) : Matrix n n k)).mulVec) :=
    funext fun x => (unipEquiv e).eq_symm_apply.2 (unipEquiv_mul_right e u x)
  rw [Measure.map_map (measurable_mul_const u) hΦ, h2,
    ← Measure.map_map hΦ ((measurable_const_add _).comp hm),
    ← Measure.map_map (measurable_const_add _) hm, h1, map_add_left_eq_self]

end Measure

theorem haar_isMulRightInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] (μ : Measure (unipRad k e)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e _ _ μ _
  borelize k
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace (unipRad k e) := (unipHomeo e).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k e) := (unipHomeo e).secondCountableTopology
  haveI := isHaarMeasure_map e (Measure.addHaar : Measure k)
  haveI := isMulRightInvariant_map e (Measure.addHaar : Measure k)
  rw [Measure.isMulLeftInvariant_eq_smul μ
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => (Measure.addHaar : Measure k)))]
  infer_instance

end GlobalTheory.SmGL.UnipHaar
end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvSepI

section

@[expose] public section

noncomputable section

open MeasureTheory Topology ValuativeRel GlobalTheory.LocLanglands GlobalTheory.LocLanglands.InvInt
open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

namespace DiscreteGroups.sglob.LConv

theorem exists_pos_invariant_form {G : Type} [Group G] {H : Subgroup G} [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (hH : IsClosed (H : Set G))
    (uG : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsUnimodular G) (uH : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsUnimodular H) :
    ∃ I : (G → ℂ) →ₗ[ℂ] ℂ,
      ∀ f : G → ℂ, (∀ u ∈ H, ∀ g, f (u * g) = f g) → Continuous f →
        (∃ C : Set G, IsCompact C ∧ ∀ g, f g ≠ 0 → ∃ u ∈ H, ∃ c ∈ C, g = u * c) →
        (∀ x, I (fun g => f (g * x)) = I f) ∧
        I (fun g => (starRingEnd ℂ) (f g)) = (starRingEnd ℂ) (I f) ∧
        ((∀ g, 0 ≤ (f g).re) → 0 ≤ (I f).re ∧ ((I f).re = 0 → ∀ g, (f g).re = 0)) := by
  borelize (G ⧸ H)
  obtain ⟨⟨μ, hμ⟩, -⟩ := GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause G H hH uG uH
  have := hμ.finiteOnCompacts
  have := hμ.invariant
  have := hμ.regular
  have : μ.IsOpenPosMeasure := ⟨fun U hU hne =>
    (measure_isOpen_pos_of_smulInvariant_of_ne_zero G hμ.ne_zero hU hne).ne'⟩
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {f | Integrable (descend H f) μ}
      zero_mem' := by simp
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
        exact hf.add hg
      smul_mem' := fun c f hf => by
        simp only [Set.mem_ofPred_eq, map_smul] at *
        exact hf.smul c }
  let J : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ q, descend H f q ∂μ
      map_add' := fun f g => integral_add f.2 g.2
      map_smul' := fun c f => integral_smul c (descend H f) }
  obtain ⟨I, hI⟩ := J.exists_extend
  have hIJ : ∀ f, Integrable (descend H f) μ → I f = ∫ q, descend H f q ∂μ := fun f hf =>
    LinearMap.congr_fun hI ⟨f, hf⟩
  refine ⟨I, fun f hf hc ⟨C, hC, hs⟩ => ?_⟩
  have hcd := continuous_descend hf hc
  have h1 : Integrable (descend H f) μ :=
    hcd.integrable_of_hasCompactSupport (hasCompactSupport_descend hf hC hs)
  refine ⟨fun x => ?_, ?_, fun hpos => ?_⟩
  · have h2 : Integrable (descend H fun g => f (g * x)) μ := by
      rw [descend_mul_right hf]
      exact (measurePreserving_smul x⁻¹ μ).integrable_comp_of_integrable h1
    rw [hIJ _ h1, hIJ _ h2, descend_mul_right hf]
    exact integral_smul_eq_self (descend H f)
  · have h2 : Integrable (descend H fun g => (starRingEnd ℂ) (f g)) μ :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp h1
    rw [hIJ _ h1, hIJ _ h2, ← integral_conj]
    rfl
  · have hre : (I f).re = ∫ q, (descend H f q).re ∂μ := by
      rw [hIJ _ h1]
      exact (integral_re h1).symm
    have hnn : 0 ≤ fun q => (descend H f q).re := fun q => hpos _
    refine ⟨hre ▸ integral_nonneg hnn, fun h0 g => ?_⟩
    rw [hre] at h0
    have hae := (integral_eq_zero_iff_of_nonneg hnn h1.re).1 h0
    have hz := (Continuous.ae_eq_iff_eq μ (Complex.continuous_re.comp hcd) continuous_zero).1 hae
    have := congrFun hz ((g⁻¹ : G) : G ⧸ H)
    simpa [descend_mk hf] using this

theorem exists_pos_isInvIntegral (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m : ℕ) :
    ∃ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I ∧
      (∀ f, IsTestFun f → I (fun g => (starRingEnd ℂ) (f g)) = (starRingEnd ℂ) (I f)) ∧
      ∀ f, IsTestFun f → (∀ g, 0 ≤ (f g).re) → 0 ≤ (I f).re ∧ ((I f).re = 0 → ∀ g, (f g).re = 0) := by
  borelize k
  obtain ⟨I, h⟩ := exists_pos_invariant_form (H := unipB k (Fin m)) isClosed_unipB
    (fun μ _ => inferInstance)
    (fun μ hμ => @UnipHaar.haar_isMulRightInvariant k _ _ _ _ (Fin m) (Fin m) (fun _ => Unit) _ _ _ _ _ _
      (points (Fin m)) (inferInstance : MeasurableSpace (unipB k (Fin m)))
      (inferInstance : BorelSpace (unipB k (Fin m))) μ hμ)
  exact ⟨I, fun f hf => (h f hf.1 hf.2.1.continuous hf.2.2).1,
    fun f hf => (h f hf.1 hf.2.1.continuous hf.2.2).2.1, fun f hf => (h f hf.1 hf.2.1.continuous hf.2.2).2.2⟩

end DiscreteGroups.sglob.LConv

end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvSepT

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ}
  {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B)

def WSp : Submodule ℂ (GL (Fin m) k → ℂ) where
  carrier := Set.range (Wf ψ hψ I B)
  zero_mem' := ⟨0, Wf_eq_zero hψ hI hB (by simp)⟩
  add_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
    exact ⟨y + z, Wf_add hψ hI hB y z⟩
  smul_mem' := by
    rintro c _ ⟨y, rfl⟩
    exact ⟨(starRingEnd ℂ) c • y, by rw [Wf_smul hψ hI hB, Complex.conj_conj]⟩

def Phi (y : WT (m := m) ψ) : WSp hψ hI hB := ⟨Wf ψ hψ I B y, y, rfl⟩

def tauRep : Representation ℂ (GL (Fin m) k) (WSp hψ hI hB) where
  toFun x :=
    { toFun := fun w => ⟨fun g => (w : GL (Fin m) k → ℂ) (g * x), by
        obtain ⟨y, hy⟩ := w.2
        exact ⟨rhoW ψ x y, funext fun g => by rw [← Wf_right hψ, hy]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext w g
    simp
  map_mul' x y := by
    ext w g
    simp [mul_assoc]

theorem tauRep_apply (x : GL (Fin m) k) (w : WSp hψ hI hB) (g : GL (Fin m) k) :
    ((tauRep hψ hI hB x w : WSp hψ hI hB) : GL (Fin m) k → ℂ) g = (w : GL (Fin m) k → ℂ) (g * x) := rfl

theorem tauRep_Phi (x : GL (Fin m) k) (y : WT (m := m) ψ) :
    tauRep hψ hI hB x (Phi hψ hI hB y) = Phi hψ hI hB (rhoW ψ x y) :=
  Subtype.ext (funext fun g => Wf_right hψ y g x)

theorem isSmooth_tau : IsSmooth (tauRep hψ hI hB) := fun w => by
  obtain ⟨y, hy⟩ := w.2
  obtain ⟨K, hKo, -, hK⟩ := exists_fix y
  let S : Subgroup (GL (Fin m) k) :=
    { carrier := {g | tauRep hψ hI hB g w = w}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : K ≤ S := fun κ hκ => by
    show tauRep hψ hI hB κ w = w
    refine Subtype.ext (funext fun g => ?_)
    rw [tauRep_apply, ← hy, Wf_right hψ, hK κ hκ]
  exact Subgroup.isOpen_mono hle hKo

theorem isIrreducible_tau
    (hZ : ∀ Z : Submodule ℂ (WT (m := m) ψ), (∀ g, ∀ z ∈ Z, rhoW ψ g z ∈ Z) →
      (∀ z ∈ Z, B z z = 0) ∨ ∀ x : WT (m := m) ψ, ∃ z ∈ Z, B (x - z) (x - z) = 0)
    {x₀ : WT (m := m) ψ} (hx₀ : B x₀ x₀ ≠ 0) : (tauRep hψ hI hB).IsIrreducible := by
  have hne : Wf ψ hψ I B x₀ ≠ 0 := fun h => hx₀ (by rw [← repr hψ hI hB x₀ x₀, h]; simp; exact map_zero I)
  haveI : Nontrivial (WSp hψ hI hB) := ⟨⟨Phi hψ hI hB x₀, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial (Subrepresentation (tauRep hψ hI hB)) := ⟨⊥, ⊤, fun h => by
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ (WSp hψ hI hB)) this⟩
  have hPadd : ∀ a b, Phi hψ hI hB (a + b) = Phi hψ hI hB a + Phi hψ hI hB b := fun a b =>
    Subtype.ext (Wf_add hψ hI hB a b)
  have hPsmul : ∀ (c : ℂ) a, Phi hψ hI hB (c • a) = (starRingEnd ℂ) c • Phi hψ hI hB a := fun c a =>
    Subtype.ext (Wf_smul hψ hI hB c a)
  have hPof : ∀ w : WSp hψ hI hB, ∃ y, Phi hψ hI hB y = w := fun w => by
    obtain ⟨y, hy⟩ := w.2
    exact ⟨y, Subtype.ext hy⟩
  refine ⟨fun S => ?_⟩
  let Z : Submodule ℂ (WT (m := m) ψ) :=
    { carrier := {y | Phi hψ hI hB y ∈ S.toSubmodule}
      zero_mem' := by
        show Phi hψ hI hB 0 ∈ S.toSubmodule
        have : Phi hψ hI hB 0 = 0 := by rw [← zero_smul ℂ (0 : WT (m := m) ψ), hPsmul, map_zero, zero_smul]
        rw [this]; exact S.toSubmodule.zero_mem
      add_mem' := fun {a b} ha hb => by
        show Phi hψ hI hB (a + b) ∈ S.toSubmodule
        rw [hPadd]; exact S.toSubmodule.add_mem ha hb
      smul_mem' := fun c a ha => by
        show Phi hψ hI hB (c • a) ∈ S.toSubmodule
        rw [hPsmul]; exact S.toSubmodule.smul_mem _ ha }
  have hinv : ∀ g, ∀ z ∈ Z, rhoW ψ g z ∈ Z := fun g z hz => by
    show Phi hψ hI hB (rhoW ψ g z) ∈ S.toSubmodule
    rw [← tauRep_Phi]; exact S.2 g hz
  rcases hZ Z hinv with h | h
  · refine Or.inl (Subrepresentation.toSubmodule_injective ?_)
    show S.toSubmodule = ⊥
    refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
    obtain ⟨y, rfl⟩ := hPof w
    exact Subtype.ext (Wf_eq_zero hψ hI hB (h y hw))
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    show S.toSubmodule = ⊤
    refine Submodule.eq_top_iff'.2 fun w => ?_
    obtain ⟨x, rfl⟩ := hPof w
    obtain ⟨z, hz, h0⟩ := h x
    have e : Phi hψ hI hB x = Phi hψ hI hB (x - z) + Phi hψ hI hB z := by rw [← hPadd, sub_add_cancel]
    rw [e, show Phi hψ hI hB (x - z) = 0 from Subtype.ext (Wf_eq_zero hψ hI hB h0), zero_add]
    exact hz

end DiscreteGroups.sglob.LConv

end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvSep

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

theorem sepOfExtreme : SepOfExtreme := by
  intro hEx hIrr hUA k _ _ _ _ _ m
  obtain ⟨I, hI1, hI2, hI3⟩ := exists_pos_isInvIntegral k m
  have hI : PosInt I := ⟨hI1, hI2, hI3⟩
  refine ⟨I, hI1, fun ψ hψ f hf hsep => ?_⟩
  by_contra hf0
  let x₀ : WT (m := m) ψ := ⟨f, hf⟩
  have hx₀ : x₀ ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  obtain ⟨B, hBext, hBf⟩ := hEx _ _ (rhoW ψ) exists_countable_span (formI ψ I) (isInvForm_formI hI) x₀
    (formI_self_ne_zero hI hx₀)
  have hB := hBext.1
  have hZ := hIrr _ _ (rhoW ψ) isSmooth_rhoW exists_fix (fun K hKo hKc => hUA k m K hKo hKc) B hBext
  let τ : IrrRep (GL (Fin m) k) :=
    ⟨WSp hψ hI hB, tauRep hψ hI hB, isSmooth_tau hψ hI hB, isIrreducible_tau hψ hI hB hZ hBf⟩
  let l : Module.Dual ℂ τ.V := (LinearMap.proj (1 : GL (Fin m) k)).comp (WSp hψ hI hB).subtype
  have hl : IsFunctional ψ⁻¹ τ.ρ l := fun u hu w => by
    obtain ⟨y, hy⟩ := w.2
    show (w : GL (Fin m) k → ℂ) (1 * u) = _ * (w : GL (Fin m) k → ℂ) 1
    have h1 := Wf_left hψ hI hB y hu 1
    rw [mul_one] at h1
    rw [one_mul, ← hy, h1]
  have h0 := hsep τ l hl (Phi hψ hI hB x₀)
  have e : (fun g => f g * l (τ.ρ g (Phi hψ hI hB x₀))) =
      fun g => (x₀ : GL (Fin m) k → ℂ) g * Wf ψ hψ I B x₀ g := funext fun g => by
    show f g * Wf ψ hψ I B x₀ (1 * g) = f g * Wf ψ hψ I B x₀ g
    rw [one_mul]
  apply hBf
  rw [← repr hψ hI hB x₀ x₀, ← e]
  exact h0

end DiscreteGroups.sglob.LConv

end
end
end
