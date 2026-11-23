module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperatorStatement

section

@[expose] public section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.exists_localTranslation_comp_commuting_operator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : GlobalTheory.CuspRep.Op E a), ∃ (g : GL (Fin a) (w.adicCompletion E)) (T : Module.End ℂ π.V), (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T := by
  first | exact @GlobalTheory.LocFactor.exists_locRep_comp | exact GlobalTheory.LocFactor.exists_locRep_comp | (intros; apply GlobalTheory.LocFactor.exists_locRep_comp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateMemTwistedJacquetKernelRamified

section

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CartanCoinv

open GlobalTheory.PRep

section Gen
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)

theorem sub_mem_coinv {k : G} (hk : k ∈ K) (v : V) : ρ k v - v ∈ twKer ρ K 1 :=
  Submodule.subset_span ⟨⟨k, hk⟩, v, by simp⟩

theorem apply_mem_coinv {k : G} (hk : k ∈ K) {v : V} (hv : v ∈ twKer ρ K 1) : ρ k v ∈ twKer ρ K 1 := by
  have := (twKer ρ K 1).add_mem (sub_mem_coinv ρ K hk v) hv
  simpa using this

theorem mem_coinv_of_eigen {k : G} (hk : k ∈ K) {v : V} {c : ℂ} (hc : c ≠ 1) (hv : ρ k v = c • v) :
    v ∈ twKer ρ K 1 := by
  have h := (twKer ρ K 1).smul_mem (c - 1)⁻¹ (sub_mem_coinv ρ K hk v)
  have e : (c - 1)⁻¹ • (ρ k v - v) = v := by
    have : ρ k v - v = (c - 1) • v := by rw [hv, sub_smul, one_smul]
    rw [this, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hc), one_smul]
  rwa [e] at h

end Gen

def diagUnit {R : Type} [CommRing R] {a : ℕ} (f : Fin a → Rˣ) : GL (Fin a) R where
  val := Matrix.diagonal fun i => (f i : R)
  inv := Matrix.diagonal fun i => ((f i)⁻¹ : Rˣ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

theorem exists_diag {L : Type} [Field L] (O : Subring L) {a : ℕ} (ha : 1 ≤ a) (u : Lˣ) (h1 : (u : L) ∈ O)
    (h2 : ((u⁻¹ : Lˣ) : L) ∈ O) : ∃ d ∈ Formalism.UG.GLint (Fin a) O, Matrix.GeneralLinearGroup.det d = u ∧
      ∃ f : Fin a → L, (d : Matrix (Fin a) (Fin a) L) = Matrix.diagonal f := by
  let u' : Oˣ := ⟨⟨u, h1⟩, ⟨(u⁻¹ : Lˣ), h2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  let f : Fin a → Oˣ := Function.update 1 ⟨0, ha⟩ u'
  have hm : ((Formalism.UG.bc O.subtype (diagUnit f) : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      Matrix.diagonal fun i => ((f i : O) : L) := by
    change (Matrix.diagonal fun i => (f i : O)).map O.subtype = _
    rw [Matrix.diagonal_map (map_zero _)]
    rfl
  refine ⟨Formalism.UG.bc O.subtype (diagUnit f), ⟨_, rfl⟩, ?_, _, hm⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, hm, Matrix.det_diagonal,
    Finset.prod_eq_single (⟨0, ha⟩ : Fin a)]
  · simp [f, u']
  · intro b _ hb
    simp [f, Function.update_of_ne hb]
  · simp

theorem translate_mem_twKer : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (u : (w.adicCompletion E)ˣ), 1 ≤ a → Valued.v (u : w.adicCompletion E) = 1 → χ u ≠ 1 → ∀ y : V, (∀ k ∈ GlobalTheory.LFun.KGL w (n := a), ρ k y = (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y) → ∀ g, ρ g y ∈ GlobalTheory.PRep.twKer ρ (GlobalTheory.LFun.KGL w (n := a)) 1 := by
  intro E _ _ w a V _ _ ρ χ u ha hu hχ y hy g
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  obtain ⟨ex, -, k₁, hk₁, k₂, hk₂, e⟩ :=
    Formalism.UG.Final.CartanDecomp E w a ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ g
  set D : GL (Fin a) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hDdef
  have hD : (D : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = Formalism.UG.diagPow E w ϖ ex := by
    rw [hDdef, Units.val_mul, Units.val_mul, e]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hg : g = k₁ * D * k₂ := by rw [hDdef]; group
  clear_value D
  have h1 : (u : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
    change Valued.v (u : w.adicCompletion E) ≤ 1
    exact hu.le
  have h2 : ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
    change Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  obtain ⟨d, hd, hdet, f, hf⟩ := exists_diag (Formalism.UG.Ov E w) ha u h1 h2
  have hcomm : d * D = D * d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, hf, Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hDy : ρ D y ∈ twKer ρ (GlobalTheory.LFun.KGL w (n := a)) 1 := by
    refine mem_coinv_of_eigen ρ _ hd (c := (((χ u)⁻¹ : ℂˣ) : ℂ)) ?_ ?_
    · intro h
      exact hχ (inv_eq_one.1 (Units.ext h))
    · rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hy d hd, hdet, map_smul]
  rw [hg, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hy k₂ hk₂, map_smul, map_smul]
  exact Submodule.smul_mem _ _ (apply_mem_coinv ρ _ hk₁ hDy)

end GlobalTheory.CartanCoinv
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateMemTwistedJacquetKernelRamifiedStatement

section

@[expose] public section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.translate_mem_twistedJacquetKernel_ramified : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (u : (w.adicCompletion E)ˣ), 1 ≤ a → Valued.v (u : w.adicCompletion E) = 1 → χ u ≠ 1 → ∀ y : V, (∀ k ∈ GlobalTheory.LFun.KGL w (n := a), ρ k y = (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y) → ∀ g, ρ g y ∈ GlobalTheory.PRep.twKer ρ (GlobalTheory.LFun.KGL w (n := a)) 1 := by
  first | exact @GlobalTheory.CartanCoinv.translate_mem_twKer | exact GlobalTheory.CartanCoinv.translate_mem_twKer | (intros; apply GlobalTheory.CartanCoinv.translate_mem_twKer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtOfSphericalAndTwistSpherical

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.SphTwistUnr

open GlobalTheory.PRep

theorem map_mem_twKer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
    (S : V →ₗ[ℂ] V) (hS : ∀ h, S ∘ₗ ρ h = ρ h ∘ₗ S) {v : V} (hv : v ∈ twKer ρ K 1) : S v ∈ twKer ρ K 1 := by
  have h : (twKer ρ K 1).map S ≤ twKer ρ K 1 := by
    rw [twKer, Submodule.map_span_le]
    rintro _ ⟨n, u, rfl⟩
    refine Submodule.subset_span ⟨n, S u, ?_⟩
    have := LinearMap.congr_fun (hS n) u
    simp only [LinearMap.comp_apply] at this
    simp [this]
  exact h ⟨v, hv, rfl⟩

theorem unrAt_of_isSpherical_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ξ).locRep w) (GlobalTheory.LFun.KGL w (n := a)) → ξ.UnrAt w := by
  intro E _ _ _ a ha π ξ w hB hsph
  obtain ⟨B, hB⟩ := hB
  have hS : GlobalTheory.LFun.HasSatGL w (π.locRep w) B := (CG.hasSat_mk π w B).1 hB
  have hK : IsCompact ((GlobalTheory.LFun.KGL w (n := a) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have hsm : IsSmooth (π.locRep w) := π.isSmooth_locRep w
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hS.1
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hT : ∀ g v, (π.twist ξ).locRep w g (π.toTwist ξ v) =
      ((ξ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • π.toTwist ξ (π.locRep w g v) := by
    intro g v
    rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
    rfl
  obtain ⟨y, rfl⟩ := (π.toTwist ξ).surjective z
  have hy0 : y ≠ 0 := fun h => hz0 (by rw [h]; exact (π.toTwist ξ).toLinearMap.map_zero)
  have hy : ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), π.locRep w k y =
      (((ξ.loc w (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y := by
    intro k hk
    have h1 := GlobalTheory.LGrp.mem_fixed.1 hz k hk
    rw [hT] at h1
    apply (π.toTwist ξ).injective
    rw [map_smul, ← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  by_contra hne
  obtain ⟨u, hu, hξu⟩ : ∃ u, Formalism.L2.Host.IsUnitAt w u ∧ ξ.loc w u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne h
  have hall := GlobalTheory.T.translate_mem_twistedJacquetKernel_ramified E w a π.V (π.locRep w) (ξ.loc w) u ha hu hξu y hy
  let Wl : Submodule ℂ π.V := ⨅ g, (twKer (π.locRep w) (GlobalTheory.LFun.KGL w (n := a)) 1).comap (π.locRep w g)
  have memWl : ∀ v, v ∈ Wl ↔ ∀ g, π.locRep w g v ∈ twKer (π.locRep w) (GlobalTheory.LFun.KGL w (n := a)) 1 := fun v => by
    simp [Wl, Submodule.mem_iInf]
  have stab : GlobalTheory.CuspRep.IsStable (Wl.map π.V.subtype) := by
    rintro o _ ⟨v, hv, rfl⟩
    obtain ⟨g, S, hS, ho⟩ := GlobalTheory.T.exists_localTranslation_comp_commuting_operator E a π w o
    have hv' := (memWl v).1 hv
    refine ⟨π.op o v, (memWl _).2 fun h => ?_, rfl⟩
    rw [ho, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul]
    have e := LinearMap.congr_fun (hS (h * g)) v
    simp only [LinearMap.comp_apply] at e
    rw [← e]
    exact map_mem_twKer S hS (hv' (h * g))
  rcases π.irred _ (Submodule.map_subtype_le _ _) stab with h | h
  · have h1 : (y : GlobalTheory.CuspRep.Sm E a) ∈ Wl.map π.V.subtype := ⟨y, (memWl y).2 hall, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    exact hy0 (Subtype.ext h1)
  · have h1 : (x : GlobalTheory.CuspRep.Sm E a) ∈ Wl.map π.V.subtype := by rw [h]; exact x.2
    obtain ⟨x', hx', e⟩ := h1
    obtain rfl : x' = x := Subtype.ext e
    have h2 := (memWl x').1 hx' 1
    rw [map_one, Module.End.one_apply] at h2
    exact hx0 (Submodule.disjoint_def.1 (GlobalTheory.LocGL.isCompl_fixed_twKer hsm hK).disjoint x' hx h2)

end GlobalTheory.SphTwistUnr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtOfSphericalAndTwistSphericalStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published


theorem _root_.GlobalTheory.T.heckeChar_unrAt_of_spherical_and_twist_spherical : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ξ).locRep w) (GlobalTheory.LFun.KGL w (n := a)) → ξ.UnrAt w := by
  first | exact @GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist | exact GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist | (intros; apply GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist <;> assumption)
end
end
