module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Clause3Asc
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenUnitCCOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LanglandsMultisegmentsOfSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOfSegRep2
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProductsStatement
import Mathlib.Algebra.Order.Star.Int
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.ExpBound
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.IsGenericOfEquiv

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericCommutationOfReorder

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg

section Quot

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y]
  [Module ℂ Y]

end Quot

section Main

variable {k : Type} [Field k] [TopologicalSpace k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem isGeneric_of_surjective {τ : Representation ℂ (GL (Fin N) k) W} {π : Representation ℂ (GL (Fin N) k) V}
    (q : τ.IntertwiningMap π) (hq : Function.Surjective q) (h : IsGeneric π) : IsGeneric τ := by
  obtain ⟨ψ, h1, h2, h3⟩ := h
  refine ⟨ψ, h1, h2, nontrivial_twJacquet_of_surjective q.toLinearMap hq
    (fun u v => Submodule.subset_span ⟨u, q v, ?_⟩) h3⟩
  rw [map_sub, map_smul]
  exact congrArg (· - _) (q.isIntertwining _ _ _ v)

end Main

end GlobalTheory.CompanionTheory.BZSeg

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.LocalComponentGL

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RSHS.LocalComponentGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem isDiscrete_of_cusp {a : ℕ} {π : CuspSub E a} (hu : π.IsUnitary) (hn : IsNormalised π) : IsDiscrete π.V := by
  refine ⟨fun φ hφ => (π.cusp φ hφ).1, fun φ hφ => ?_, π.stable, π.ne_bot, π.irred⟩
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_isUnitary hu hφ
  exact GlobalTheory.DiscChar.isSqInt_of_bounded (hn φ hφ) hC

theorem locCompGL_of_locComp {a : ℕ} {π : CuspSub E a} {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) : IsLocCompGL π.V w σ := by
  obtain ⟨f, h0, h1⟩ := hσ
  exact ⟨π.V.subtype.comp f, fun e => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun e v)),
    fun v => (f v).2, fun g v => congrArg Subtype.val (h1 g v)⟩

theorem generic_unitarisable {a : ℕ} {π : CuspSub E a} (hu : π.IsUnitary) (hn : IsNormalised π)
    {w : HeightOneSpectrum (𝓞 E)} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) :
    GlobalTheory.LocGL.IsGeneric (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred).rep ∧
      GlobalTheory.SmGL.IsUnitarisable (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred).rep := by
  let e := GlobalTheory.LocGL.IrrGL.equivOf σ.ρ σ.smooth σ.irred
  have hg : GlobalTheory.LocGL.IsGeneric σ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E a π w σ hσ
  have hv : GlobalTheory.SmGL.IsUnitarisable σ.ρ :=
    GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E a π.V (isDiscrete_of_cusp hu hn) w σ
      (locCompGL_of_locComp hσ)
  exact ⟨GlobalTheory.CompanionTheory.BZSeg.isGeneric_of_surjective e.symm.toIntertwiningMap e.symm.toLinearEquiv.surjective hg,
    GlobalTheory.GenericUnitary.isUnitarisable_of_equiv e hv⟩

end PositivityTheory.RSHS.LocalComponentGL

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.SpehCosocleUc

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.Rg.Rs.C3.UC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}



theorem spehCosocle_uc (hG : PositivityTheory.RgUd.Exp.GenUnitCC) (hSC : GlobalTheory.Published.StandardCosocleGL)
    [CharZero k] (x : GlobalTheory.LocGL.IrrGL (k := k)) (hg : GlobalTheory.LocGL.IsGeneric x.rep)
    (hu : GlobalTheory.SmGL.IsUnitarisable x.rep) (d : ℕ) (hd : ∑ i, (GlobalTheory.LocGL.spehFactor x d i).1 = N) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ (GL (Fin N) k) W),
      GlobalTheory.LocGL.IsCosocle τ (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd) := by
  obtain ⟨m, δ, Δ, s, hΔ, hδu, hs, hd0, ⟨φ⟩⟩ := hG k _ _ x.rep x.2.rep.smooth x.2.rep.irr hu hg
  let y : Fin d → Fin m → IrrGL (k := k) := fun i j => ((δ j).nu (s j)).nu (((d : ℂ) - 1) / 2 - (i : ℕ))
  have hN : ∀ i, ∑ j, (y i j).1 = (spehFactor x d i).1 := fun _ => hd0
  let Y : Fin (d * m) → IrrGL (k := k) := fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  have hM' : ∑ p, (Y p).1 = N := by
    rw [← hd, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Y, Equiv.symm_apply_apply]
    exact hN i
  let e1 : ∀ i : Fin d, (spehFactor x d i).rep.Equiv (prodIrr (y i) (hN i)) := fun i =>
    (x.twEquiv _ (isSmoothChar_absPow _)).symm.trans
      ((twistEquiv φ _).trans (prodIrrTwistEquiv _ hd0 _ (isSmoothChar_absPow _)))
  obtain ⟨e2⟩ := GlobalTheory.T.parabolicInduction_in_stages_product_of_products k d m y (fun i => (spehFactor x d i).1) N hN hd hM'
  let E := (multiProdEquiv _ e1).trans e2
  let Γs : Fin (d * m) → Segment k := fun p =>
    ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)
  have hcast : ∀ i : ℕ, (((((d : ℝ) - 1) / 2 - i : ℝ)) : ℂ) = ((d : ℂ) - 1) / 2 - (i : ℕ) := fun i => by
    push_cast; ring
  have hL : ∀ p, IsLSeg (Γs p) (Y p).rep := fun p => by
    simp only [Γs, Y, y, hcast]
    exact GlobalTheory.isLSeg_nu (GlobalTheory.isLSeg_nu (hΔ _) _) _
  have hord : ∀ p p' : Fin (d * m), p < p' → ¬ (Γs p).Precedes (Γs p') := by
    intro p p' hpp' hP
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective p'
    have hii : (i : ℕ) ≤ i' := by
      by_contra hlt
      have h1 : (i' : ℕ) + 1 ≤ i := by omega
      have h2 := Nat.mul_le_mul_left m h1
      have h3 := Fin.lt_def.1 hpp'
      simp only [finProdFinEquiv_apply_val] at h3
      have := j.2
      have := j'.2
      nlinarith
    simp only [Γs, Equiv.symm_apply_apply, GlobalTheory.segment_nu_nu] at hP
    have key := PositivityTheory.RgUd.UOrder.add_one_le_of_precedes_u k (δ j) (δ j') (Δ j) (Δ j') (hΔ j) (hδu j) (hΔ j')
      (hδu j') (s j + (((d : ℝ) - 1) / 2 - (i : ℕ))) (s j' + (((d : ℝ) - 1) / 2 - (i' : ℕ)))
      (by push_cast at hP ⊢; exact hP)
    have hi : ((i : ℕ) : ℝ) ≤ (i' : ℕ) := by exact_mod_cast hii
    have := abs_lt.1 (hs j)
    have := abs_lt.1 (hs j')
    linarith
  have hLF : LFactors (↑((List.range d).flatMap fun i : ℕ =>
      (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ))) Y :=
    ⟨Γs, ⟨GlobalTheory.univ_map_speh_segments d m Δ s, hord⟩, hL⟩
  obtain ⟨π, hπ⟩ := hSC k _ (d * m) N Y hM' hLF
  exact ⟨_, _, _, π.ρ, hπ.of_equiv (.refl _) E.symm⟩

end PositivityTheory.Rg.Rs.C3.UC

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.CharZeroCompletion

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3

theorem isSpeh_of_quot {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin N) k) V}
    (hi : ρ.IsIrreducible) (x : GlobalTheory.LocGL.IrrGL (k := k)) (d : ℕ)
    (hd : ∑ i, (GlobalTheory.LocGL.spehFactor x d i).1 = N)
    (hc : ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ (GL (Fin N) k) W),
      GlobalTheory.LocGL.IsCosocle τ (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd))
    (f : (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd).IntertwiningMap ρ) (hf : Function.Surjective f) :
    GlobalTheory.LocGL.IsSpeh x d ρ := by
  obtain ⟨W, _, _, τ, hτ⟩ := hc
  obtain ⟨e⟩ := hτ.equiv_of_surjective hi f hf
  exact ⟨hd, hτ.of_equiv e.symm (.refl _)⟩

theorem charZero_completion {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

theorem clause3Asc_of (hL : LocSub) (hD : LocDual) (hG : PositivityTheory.RgUd.Exp.GenUnitCC)
    (hSC : GlobalTheory.Published.StandardCosocleGL) : Clause3Asc := by
  intro E _ _ _ N a d V π hN hV hu hn hasc w σ σ' hσ hσ'
  obtain ⟨hd, f, hf⟩ := hL E N a d V π hN hV hasc w σ σ' hσ hσ'
  obtain ⟨hg, hun⟩ := PositivityTheory.RSHS.LocalComponentGL.generic_unitarisable hu hn hσ
  have hU' : IsUnitarisable σ'.ρ := GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E N V hV w σ' hσ'
  have := charZero_completion (E := E) w
  obtain ⟨hd', g, hg'⟩ := hD _ N d _ σ' hun hU' hd f hf
  exact isSpeh_of_quot σ'.irred _ d hd' (UC.spehCosocle_uc hG hSC _ hg hun d hd') g hg'

theorem clause3Asc_holds (hL : LocSub) (hD : LocDual) : Clause3Asc :=
  have hZ := PositivityTheory.RgGu.segmentRepresentation
  clause3Asc_of hL hD
    (PositivityTheory.RgUd.Exp.genUnitCCOf (fun k _ _ _ _ => PositivityTheory.RgUd.expBound k) (GlobalTheory.RgGu.genericUnlinkedGL_of_segRep2 hZ))
    (PositivityTheory.Exh.standardCosocleGL_of_seg hZ)

end PositivityTheory.Rg.Rs.C3

end
end
end
