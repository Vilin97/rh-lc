module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatakeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexConjugateCuspidalRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDualC

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRepStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.exists_invariant_hermitianForm_cuspidalRep : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) ∧ (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) ∧ (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) ∧ (∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ) ∧ ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0 := by
  first | exact @GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian | exact GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian | (intros; apply GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParameterGLOfConjLinearIntertwiner

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.LFun.SatConj

open ComplexConjugate

theorem esymm_map_conj (s : Multiset ℂ) (j : ℕ) : (s.map (starRingEnd ℂ)).esymm j = conj (s.esymm j) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun t _ => ?_
  simp [map_multiset_prod]

theorem conj_satEig (q n : ℕ) (B : Multiset ℂˣ) (j : ℕ) :
    conj (GlobalTheory.LFun.satEig q n B j) = GlobalTheory.LFun.satEig q n (B.map star) j := by
  have hz : conj (((j : ℂ) * ((n : ℂ) - j)) / 2) = ((j : ℂ) * ((n : ℂ) - j)) / 2 := by
    rw [map_div₀, map_mul, map_sub, Complex.conj_natCast, Complex.conj_natCast, map_ofNat]
  have harg : (q : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_pos.ne
  have hp : conj ((q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2)) = (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) := by
    have := Complex.conj_cpow (q : ℂ) (((j : ℂ) * ((n : ℂ) - j)) / 2) harg
    rw [hz, Complex.conj_natCast] at this
    exact this.symm
  have hm : ((B.map star).map fun b : ℂˣ => (b : ℂ)) = (B.map fun b : ℂˣ => (b : ℂ)).map (starRingEnd ℂ) := by
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [Units.coe_star]
  rw [GlobalTheory.LFun.satEig, GlobalTheory.LFun.satEig, map_mul, hp, hm, esymm_map_conj]

theorem conj_Tj {L : Type} [Field L] (n : ℕ) (O : Subring L) (ϖ : L) (j : ℕ) (g : GL (Fin n) L) :
    conj (Formalism.UG.Tj ℂ n O ϖ j g) = Formalism.UG.Tj ℂ n O ϖ j g := by
  classical
  unfold Formalism.UG.Tj
  rw [Set.indicator_apply]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}
  {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}

theorem isSatVecGL_conj (J : V ≃ₗ⋆[ℂ] W) (hJ : ∀ g x, ρ' g (J x) = J (ρ g x)) {x : V} {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.IsSatVecGL w ρ x B) : GlobalTheory.LFun.IsSatVecGL w ρ' (J x) (B.map star) := by
  obtain ⟨h0, hfix, hcard, hT⟩ := h
  refine ⟨fun e => h0 (J.map_eq_zero_iff.1 e), GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [hJ, GlobalTheory.LGrp.mem_fixed.1 hfix k hk], by simp [hcard], fun ϖ hϖ j hj => ?_⟩
  have hfin := GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ x
  have e1 : GlobalTheory.LFun.heckeVec ρ' (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) (J x) =
      J (GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) x) := by
    rw [GlobalTheory.LFun.heckeVec, GlobalTheory.LFun.heckeVec]
    refine (finsum_congr fun c => ?_).trans
      (AddMonoidHom.map_finsum (J.toLinearMap.toAddMonoidHom) hfin).symm
    simp [hJ, conj_Tj]
  rw [e1, hT ϖ hϖ j hj, LinearEquiv.map_smulₛₗ, conj_satEig]

end GlobalTheory.LFun.SatConj


open GlobalTheory.LFun.SatConj in
theorem GlobalTheory.LFun.hasSatGL_of_conjIntertwiner : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W) (J : V ≃ₗ⋆[ℂ] W), (∀ g x, ρ' g (J x) = J (ρ g x)) → ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B → GlobalTheory.LFun.HasSatGL w ρ' (B.map star) := by
  intro E _ _ w n V W _ _ _ _ ρ ρ' J hJ B hB
  have hJs : ∀ g y, ρ g (J.symm y) = J.symm (ρ' g y) := fun g y => by
    apply J.injective
    rw [← hJ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ := hB.exists_vec
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨J x, (isSatVecGL_conj J hJ hx).2.1, (isSatVecGL_conj J hJ hx).1⟩,
    fun y hy h0 => ?_⟩
  have hy' : J.symm y ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := n)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [hJs, GlobalTheory.LGrp.mem_fixed.1 hy k hk]
  have := isSatVecGL_conj J hJ (hB.2 _ hy' fun e => h0 (by simpa using congrArg J e))
  rwa [LinearEquiv.apply_symm_apply] at this
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParameterGLOfConjLinearIntertwinerStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.satake_parameter_GL_of_conj_linear_intertwiner : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W) (J : V ≃ₗ⋆[ℂ] W), (∀ g x, ρ' g (J x) = J (ρ g x)) → ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B → GlobalTheory.LFun.HasSatGL w ρ' (B.map star) := by
  first | exact @GlobalTheory.LFun.hasSatGL_of_conjIntertwiner | exact GlobalTheory.LFun.hasSatGL_of_conjIntertwiner | (intros; apply GlobalTheory.LFun.hasSatGL_of_conjIntertwiner <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCuspidalSatakeParameterStarEqInv

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CuspRep.UnitaryParam

theorem map_star_eq_map_inv_of_form : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) → (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) → ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → B.map star = B.map (·⁻¹) := by
  intro E _ _ _ a π H hH hpos hinv w B hB
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
  refine GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w a π.V (π.locRep w) x B ?_ hx
  refine ⟨H.flip, fun v u => ?_, fun v hv => ?_, fun g v u => ?_⟩
  · simp only [LinearMap.flip_apply]
    exact (hH u v).symm
  · simpa only [LinearMap.flip_apply] using hpos v hv
  · simp only [LinearMap.flip_apply]
    exact hinv _ u v

end GlobalTheory.CuspRep.UnitaryParam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCuspidalSatakeParameterStarEqInvStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.unitary_cuspidal_satake_parameter_star_eq_inv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) → (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) → ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → B.map star = B.map (·⁻¹) := by
  first | exact @GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form | exact GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form | (intros; apply GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepPairedWithItself

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.GKPair

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem map_inv_map_star {B : Multiset ℂˣ} (h : B.map star = B.map (·⁻¹)) : (B.map (·⁻¹)).map star = B := by
  have e : (B.map (·⁻¹)).map star = (B.map star).map (·⁻¹) := by
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun u _ => ?_
    exact Units.ext (by simp)
  rw [e, h, Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id B]
  exact Multiset.map_congr rfl fun u _ => inv_inv u

theorem paired_of_form (π : CuspSub E a) (L : π.V ≃ₗ⋆[ℂ] π.V)
    (hL : ∀ o ψ, L (π.op (invTOp o) ψ) = π.op o (L ψ)) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ)
    (hpos : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hfin : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ)
    (hcpt : ∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ)
    (hlie : ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0) :
    Paired π π invTOp := by
  let B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ := (H.comp L.toLinearMap).flip
  have hB : ∀ φ ψ, B φ ψ = H (L ψ) φ := fun _ _ => rfl
  have h0 : ∀ φ, H φ φ = 0 → φ = 0 := fun φ h => by
    by_contra hφ
    have := hpos φ hφ
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨B, fun φ h => h0 φ ?_, fun ψ h => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · have := h (L.symm φ)
    rwa [hB, LinearEquiv.apply_symm_apply] at this
  · have := h (L ψ)
    rw [hB] at this
    exact (map_eq_zero_iff L L.injective).1 (h0 _ this)
  · rw [hB, hB, hL, hfin]
  · rw [hB, hB, hL, hcpt]
  · rw [hB, hB, hL, add_comm]
    exact hlie X (L ψ) φ

theorem paired_invTOp (hJS : GlobalTheory.Published.JacquetShalikaRigidity) (hB : GlobalTheory.Published.CuspFormsBoundedGL)
    (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ha : 1 ≤ a) (π : CuspSub E a) (hπ : GlobalTheory.DiscSpec.IsNormalised π) : Paired π π invTOp := by
  obtain ⟨H, hH, hpos, hfin, hcpt, hlie⟩ := GlobalTheory.T.exists_invariant_hermitianForm_cuspidalRep hB E a π hπ
  obtain ⟨π₂, J, hJ⟩ := GlobalTheory.T.exists_complex_conjugate_cuspidal_representation E a (UpperTheory.V.TC.dual π)
  have hsat : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk π₂).HasSat w B ∧ (CG.mk π).HasSat w B := by
    refine (GlobalTheory.T.cuspidal_GL_local_components_eventually_satake hA E a π).mono fun w ⟨B, hBw⟩ => ⟨B, ?_, hBw⟩
    have h1 := UpperTheory.V.TC.hasSatGL_dual hBw
    have h2 := GlobalTheory.T.satake_parameter_GL_of_conj_linear_intertwiner E w a _ _ ((UpperTheory.V.TC.dual π).locRep w) (π₂.locRep w) J
      (fun g x => by rw [CuspSub.locRep_eq, CuspSub.locRep_eq, hJ]) _ h1
    have h3 := GlobalTheory.T.unitary_cuspidal_satake_parameter_star_eq_inv E a π H hH hpos hfin w B hBw
    rw [map_inv_map_star h3] at h2
    exact h2
  have e := hJS.strong_multiplicity_one ha (CG.mk π₂) (CG.mk π) hsat
  obtain ⟨T, hT⟩ : CuspSub.Iso π₂ π := Quotient.exact e
  let L : π.V ≃ₗ⋆[ℂ] π.V := ((UpperTheory.V.TC.toDual π).trans J).trans T
  refine paired_of_form π L (fun o ψ => ?_) H hpos hfin hcpt hlie
  change T (J (UpperTheory.V.TC.toDual π (π.op (invTOp o) ψ))) = π.op o (T (J (UpperTheory.V.TC.toDual π ψ)))
  rw [← UpperTheory.V.TC.op_toDual, hJ, hT]

end GlobalTheory.GKPair
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepPairedWithItselfStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.cusp_rep_paired_with_itself : GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.CuspFormsBoundedGL → GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, GlobalTheory.DiscSpec.IsNormalised π → Paired π π invTOp := by
  first | exact @GlobalTheory.GKPair.paired_invTOp | exact GlobalTheory.GKPair.paired_invTOp | (intros; apply GlobalTheory.GKPair.paired_invTOp <;> assumption)
end
end
