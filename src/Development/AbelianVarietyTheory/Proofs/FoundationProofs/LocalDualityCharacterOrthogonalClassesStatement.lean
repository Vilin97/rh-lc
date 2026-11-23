module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfOrthogonalDualCharacterModPrimePowStatement
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAnnihilatorDepthOfNotCoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulScalarClassEqSmulAddCoboundaryModPrimePStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitCharacterOfIntegralCyclotomicProduct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLePowIffDvd
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfUniformLimitCoboundaries

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory

theorem coboundary_closed_of_uniform_approx {𝕜 : Type} [NormedField 𝕜] {Γ : Type} (H : Set Γ)
    (k f : Γ → 𝕜) (hne : ∃ s ∈ H, k s ≠ 1)
    (happ : ∀ ε : ℝ, 0 < ε → ∃ X : 𝕜, ∀ s ∈ H, ‖f s - (k s * X - X)‖ ≤ ε) :
    ∃ X : 𝕜, ∀ s ∈ H, f s = k s * X - X := by
  obtain ⟨s₀, hs₀, hk⟩ := hne
  have hd : k s₀ - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hdpos : 0 < ‖k s₀ - 1‖ := norm_pos_iff.mpr hd
  refine ⟨f s₀ / (k s₀ - 1), fun s hs => ?_⟩
  have hCpos : 0 < 1 + ‖k s - 1‖ / ‖k s₀ - 1‖ := by positivity
  have key : ∀ ε : ℝ, 0 < ε → ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖
      ≤ ε * (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) := by
    intro ε hε
    obtain ⟨X, hX⟩ := happ ε hε
    have h0 := hX s₀ hs₀
    have e0 : f s₀ - (k s₀ * X - X) = (k s₀ - 1) * (f s₀ / (k s₀ - 1) - X) := by
      field_simp
    rw [e0, norm_mul] at h0
    have hXX : ‖X - f s₀ / (k s₀ - 1)‖ ≤ ε / ‖k s₀ - 1‖ := by
      rw [norm_sub_rev, le_div_iff₀ hdpos, mul_comm]; exact h0
    have e1 : f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))
        = (f s - (k s * X - X)) + (k s - 1) * (X - f s₀ / (k s₀ - 1)) := by ring
    calc ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖
        = ‖(f s - (k s * X - X)) + (k s - 1) * (X - f s₀ / (k s₀ - 1))‖ := by rw [e1]
      _ ≤ ‖f s - (k s * X - X)‖ + ‖k s - 1‖ * ‖X - f s₀ / (k s₀ - 1)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ ε + ‖k s - 1‖ * (ε / ‖k s₀ - 1‖) := by
          gcongr
          exact hX s hs
      _ = ε * (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) := by ring
  have hz : ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h := key (ε / (1 + ‖k s - 1‖ / ‖k s₀ - 1‖)) (div_pos hε hCpos)
    rw [div_mul_cancel₀ _ hCpos.ne'] at h
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfUniformLimitCoboundariesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.coboundary_of_uniform_limit_coboundaries : ∀ {𝕜 : Type} [NormedField 𝕜] {Γ : Type} (H : Set Γ) (k f : Γ → 𝕜), (∃ s ∈ H, k s ≠ 1) → (∀ ε : ℝ, 0 < ε → ∃ X : 𝕜, ∀ s ∈ H, ‖f s - (k s * X - X)‖ ≤ ε) → ∃ X : 𝕜, ∀ s ∈ H, f s = k s * X - X := by
  first | exact @GlobalTheory.coboundary_closed_of_uniform_approx | exact GlobalTheory.coboundary_closed_of_uniform_approx | (intros; apply GlobalTheory.coboundary_closed_of_uniform_approx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitCharacterOfIntegralCyclotomicProductStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' : G ℚ Ω → Qbar l), ContinuousOn k (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t) → ∃ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧ ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = k g := by
  first | exact @GlobalTheory.LocChar.unit_of_integral | exact GlobalTheory.LocChar.unit_of_integral | (intros; apply GlobalTheory.LocChar.unit_of_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLePowIffDvdStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.norm_le_pow_iff_dvd : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (x : c.O), ‖((x : c.O) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ ↔ ((l : ℕ) : c.O) ^ n ∣ x := by
  first | exact @GlobalTheory.Coef.norm_le_norm_pow_iff_dvd | exact GlobalTheory.Coef.norm_le_norm_pow_iff_dvd | (intros; apply GlobalTheory.Coef.norm_le_norm_pow_iff_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalDualityCharacterOrthogonalClasses

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.Ord2.localDuality_char : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' a b : G ℚ Ω → Qbar l), OverL l A → ContinuousOn k (Dec (F := ℚ) A) → ContinuousOn k' (Dec (F := ℚ) A) → ContinuousOn a (Dec (F := ℚ) A) → ContinuousOn b (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ a s ∈ c.O ∧ b s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t ∧ k' (s * t) = k' s * k' t ∧ b (s * t) = b s + k s * b t ∧ a (s * t) = a s + k' s * a t) → (∃ s ∈ Dec (F := ℚ) A, k s ≠ 1) → (∃ s ∈ Dec (F := ℚ) A, k' s ≠ 1) → (∀ n : ℕ, Cob2 c n (Dec (F := ℚ) A) (fun s t => b s * (k' s * a t))) → (∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, b s = k s * x - x) ∨ ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x := by
  intro hL l _ Ω _ _ _ c A k k' a b hA hk hk' ha hb hint hmul hk1 hk'1 hcob
  by_cases hac : ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x
  · exact Or.inr hac
  left
  obtain ⟨θ, hθc, hθ⟩ := GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product l Ω c A k k' hk
    (fun s hs => ⟨(hint s hs).1, (hint s hs).2.1, (hint s hs).2.2.2.2⟩) (fun s hs t ht => (hmul s hs t ht).1)
  obtain ⟨θ', hθ'c, hθ'⟩ := GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product l Ω c A k' k hk'
    (fun s hs => ⟨(hint s hs).2.1, (hint s hs).1, by rw [mul_comm]; exact (hint s hs).2.2.2.2⟩)
    (fun s hs t ht => (hmul s hs t ht).2.1)
  have hN := GlobalTheory.T.norm_le_pow_iff_dvd l c
  have hchi : ∀ s : G ℚ Ω, ((((UpperTheory.V.Base.chiO ℚ Ω l c.O) s : c.Oˣ) : c.O) : Qbar l) = eps l s := by
    intro s; rfl
  have hcyc : θ * θ' = (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype := by
    refine MonoidHom.ext fun g => Units.ext (Subtype.ext ?_)
    simp only [MonoidHom.mul_apply, Units.val_mul, Subalgebra.coe_mul, hθ, hθ', MonoidHom.comp_apply,
      Subgroup.coe_subtype, hchi]
    exact (hint g g.2).2.2.2.2
  have hθ1 : ∃ g, θ g ≠ 1 := by
    obtain ⟨s, hs, hne⟩ := hk1
    exact ⟨⟨s, hs⟩, fun h => hne (by have e := hθ ⟨s, hs⟩; rw [h] at e; exact e.symm.trans rfl)⟩
  have hθ'1 : ∃ g, θ' g ≠ 1 := by
    obtain ⟨s, hs, hne⟩ := hk'1
    exact ⟨⟨s, hs⟩, fun h => hne (by have e := hθ' ⟨s, hs⟩; rw [h] at e; exact e.symm.trans rfl)⟩
  have hθ'ne : ∃ g, θ' g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g := by
    obtain ⟨s, hs, hne⟩ := hk1
    refine ⟨⟨s, hs⟩, fun h => hne ?_⟩
    have e := DFunLike.congr_fun hcyc ⟨s, hs⟩
    rw [MonoidHom.mul_apply, ← h] at e
    have e1 : θ ⟨s, hs⟩ = 1 := mul_eq_right.1 e
    have e2 := hθ ⟨s, hs⟩; rw [e1] at e2; exact e2.symm.trans rfl
  set p : c.O := ((l : ℕ) : c.O) with hp
  let aO : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨a s, (hint s.1 s.2).2.2.1⟩
  let bO : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨b s, (hint s.1 s.2).2.2.2.1⟩
  have haO : Continuous aO := (continuousOn_iff_continuous_domRestrict.1 ha).subtype_mk _
  have hbO : Continuous bO := (continuousOn_iff_continuous_domRestrict.1 hb).subtype_mk _
  have haOc : ∀ s t, aO (s * t) = aO s + ((θ' s : c.Oˣ) : c.O) * aO t := fun s t => Subtype.ext (by
    simp only [aO, Subalgebra.coe_add, Subalgebra.coe_mul, hθ']
    exact (hmul s.1 s.2 t.1 t.2).2.2.2)
  have hbOc : ∀ s t, bO (s * t) = bO s + ((θ s : c.Oˣ) : c.O) * bO t := fun s t => Subtype.ext (by
    simp only [bO, Subalgebra.coe_add, Subalgebra.coe_mul, hθ]
    exact (hmul s.1 s.2 t.1 t.2).2.2.1)
  have hnorm1 : ∀ x : c.O, ‖((x : c.O) : Qbar l)‖ ≤ 1 := fun x => by
    have := (hN 0 x).2 (by simp); simpa using this
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_annihilatorDepth_of_not_coboundary l (Set.univ : Set ↥(Dec (F := ℚ) A)) (fun s => k' s) (fun s => a s)
    (by obtain ⟨s, hs, hne⟩ := hk'1; exact ⟨⟨s, hs⟩, trivial, hne⟩)
    (fun ⟨X, hX⟩ => hac ⟨X, fun s hs => hX ⟨s, hs⟩ trivial⟩)
  have hann : ∀ n : ℕ, ∀ x y : c.O, (∀ s, p ^ n ∣ x * aO s - (((θ' s : c.Oˣ) : c.O) * y - y)) → p ^ (n - r) ∣ x := by
    intro n x y h
    refine (hN (n - r) x).1 (hr n x y (hnorm1 x) fun s _ => ?_)
    have := (hN n _).2 (h s)
    simpa [aO, hθ'] using this
  obtain ⟨m, hm0, hAF⟩ := GlobalTheory.T.exists_mul_scalarClass_eq_smul_add_coboundary_modPrimePow hL.lf hL.lt hL.le l Ω c A hA θ' hθ'c hθ'1 hθ'ne r
  have key : ∀ n : ℕ, 1 ≤ n → ∃ x : c.O, ∀ s, p ^ n ∣ (m : c.O) * bO s - (((θ s : c.Oˣ) : c.O) * x - x) := by
    intro n hn
    refine GlobalTheory.T.coboundary_of_orthogonal_dualCharacter_modPrimePow hL.lf hL.lt l Ω c A hA θ θ' hθc hθ'c hcyc n hn (fun s => (m : c.O) * bO s)
      (continuous_const.mul hbO) (fun s t => ?_) (fun a' ha' hca' => ?_)
    · rw [hbOc s t]; ring_nf; exact dvd_zero _
    obtain ⟨x, y, hxy⟩ := hAF n hn aO haO (fun s t => by rw [haOc s t, sub_self]; exact dvd_zero _)
      (hann n) a' ha' hca'
    obtain ⟨u, huc, huO, hu⟩ := hcob n
    let u0 : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨u s, huO s⟩
    have hu0c : Continuous u0 := (continuousOn_iff_continuous_domRestrict.1 huc).subtype_mk _
    have hu0 : ∀ s t, p ^ n ∣ bO s * (((θ' s : c.Oˣ) : c.O) * aO t) -
        ((((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) * u0 t - u0 (s * t) + u0 s) := by
      intro s t
      refine (hN n _).1 ?_
      have e : ‖b s.1 * (k' s.1 * a t.1) - (eps l s.1 * u t.1 - u (s.1 * t.1) + u s.1)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ :=
        hu s.1 s.2 t.1 t.2
      have he : k s.1 * k' s.1 = eps l s.1 := (hint s.1 s.2).2.2.2.2
      rw [← he] at e
      convert e using 2
      simp only [aO, bO, u0, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul, hθ, hθ']
      rfl
    have hbt : Continuous (fun s => bO s * ((θ' s : c.Oˣ) : c.O)) := hbO.mul hθ'c
    have hcu : Continuous (fun s => x * u0 s - bO s * ((θ' s : c.Oˣ) : c.O) * y) :=
      (continuous_const.mul hu0c).sub (hbt.mul continuous_const)
    refine ⟨fun s => x * u0 s - bO s * ((θ' s : c.Oˣ) : c.O) * y, hcu, fun s t => ?_⟩
    obtain ⟨q1, hq1⟩ := hxy t
    obtain ⟨q2, hq2⟩ := hu0 s t
    refine ⟨bO s * ((θ' s : c.Oˣ) : c.O) * q1 + x * q2, ?_⟩
    simp only []
    rw [hbOc s t, map_mul θ' s t, Units.val_mul]
    linear_combination (bO s * ((θ' s : c.Oˣ) : c.O)) * hq1 + x * hq2
  obtain ⟨s0, hs0, hne0⟩ := hk1
  refine GlobalTheory.T.coboundary_of_uniform_limit_coboundaries (Dec (F := ℚ) A : Set (G ℚ Ω)) k b ⟨s0, hs0, hne0⟩ fun ε hε => ?_
  have hl1 : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [e, norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hm : (0 : ℝ) < ‖((m : ℕ) : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hm0.ne')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hm) hl1
  obtain ⟨x, hx⟩ := key (n + 1) (Nat.le_add_left 1 n)
  refine ⟨(x : Qbar l) / (m : Qbar l), fun s hs => ?_⟩
  have e := (hN (n + 1) _).2 (hx ⟨s, hs⟩)
  have e2 : ((((m : c.O) * bO ⟨s, hs⟩ - (((θ ⟨s, hs⟩ : c.Oˣ) : c.O) * x - x) : c.O)) : Qbar l) =
      (m : Qbar l) * (b s - (k s * ((x : Qbar l) / (m : Qbar l)) - (x : Qbar l) / (m : Qbar l))) := by
    have hm' : (m : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hm0.ne'
    have hb' : ((bO ⟨s, hs⟩ : c.O) : Qbar l) = b s := rfl
    have hk'' : (((θ ⟨s, hs⟩ : c.Oˣ) : c.O) : Qbar l) = k s := hθ _
    push_cast [hb', hk'']
    field_simp
  rw [e2, norm_mul] at e
  have e3 : ‖((l : ℕ) : Qbar l) ^ (n + 1)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ n := by
    rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ n)
  rw [← le_div_iff₀' hm] at e
  refine e.trans ?_
  rw [div_le_iff₀ hm]
  linarith
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalDualityCharacterOrthogonalClassesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.local_duality_character_orthogonal_classes : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' a b : G ℚ Ω → Qbar l), OverL l A → ContinuousOn k (Dec (F := ℚ) A) → ContinuousOn k' (Dec (F := ℚ) A) → ContinuousOn a (Dec (F := ℚ) A) → ContinuousOn b (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ a s ∈ c.O ∧ b s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t ∧ k' (s * t) = k' s * k' t ∧ b (s * t) = b s + k s * b t ∧ a (s * t) = a s + k' s * a t) → (∃ s ∈ Dec (F := ℚ) A, k s ≠ 1) → (∃ s ∈ Dec (F := ℚ) A, k' s ≠ 1) → (∀ n : ℕ, Cob2 c n (Dec (F := ℚ) A) (fun s t => b s * (k' s * a t))) → (∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, b s = k s * x - x) ∨ ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x := by
  first | exact @GlobalTheory.Ord2.localDuality_char | exact GlobalTheory.Ord2.localDuality_char | (intros; apply GlobalTheory.Ord2.localDuality_char <;> assumption)
end
end
