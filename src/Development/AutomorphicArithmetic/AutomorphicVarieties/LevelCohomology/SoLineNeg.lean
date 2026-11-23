module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCobIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.CobDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCobLim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDecNe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLocKill
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCobPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X
open scoped Pointwise

theorem UpperTheory.V.X.So.cobPlace :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (O : Type) [CommRing O] (θ : G k Ω →* Oˣ) (z : G k Ω → O), Coc θ z → ∀ (v : HeightOneSpectrum (𝓞 k)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v → CobOn θ z (Dec (F := k) A) → CobOn θ z (Dec (F := k) A') := by
  intro k Ω _ _ _ _ _ O _ θ z hz v A A' hA hA' hcob
  obtain ⟨a, ha, m, hm⟩ := hcob
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_over hA hA'
  refine ⟨a, ha, (θ g : O) * m - a * z g, ?_⟩
  intro h hh
  obtain ⟨h0, hh0, rfl⟩ : ∃ h0 ∈ Dec (F := k) A, h = g * h0 * g⁻¹ := by
    refine ⟨g⁻¹ * h * g, ?_, by group⟩
    rw [mem_Dec] at hh ⊢
    rw [mul_smul, mul_smul, hh, inv_smul_smul]
  have e := hm h0 hh0
  have hz1 : z 1 = 0 := by
    have h11 := hz 1 1
    rw [one_mul, map_one, Units.val_one, one_mul] at h11
    linear_combination -h11
  have hinv : (θ g : O) * z g⁻¹ = - z g := by
    have h2 := hz g g⁻¹
    rw [mul_inv_cancel, hz1] at h2
    linear_combination -h2
  have hθ : θ (g * h0 * g⁻¹) = θ h0 := by
    rw [map_mul, map_mul, map_inv, mul_comm (θ g), mul_inv_cancel_right]
  rw [hθ, hz (g * h0) g⁻¹, hz g h0, map_mul, Units.val_mul]
  linear_combination (θ g : O) * e + a * (θ h0 : O) * hinv
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLocTors

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.locTors : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ n : ℤ, n ≠ 0 → n ≠ 1 → ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v → ((l : ℕ) : 𝓞 k) ∉ v.asIdeal → ∀ z : G k Ω → O, Coc (ψ * chiO k Ω l O ^ n) z → Alg.AdicCont (maximalIdeal O) z → CobOn (ψ * chiO k Ω l O ^ n) z (Dec (F := k) A) := by
  intro lf lt le k Ω _ _ _ _ _ l hl O _ _ _ _ _ ψ ho n h0 h1 v A hA hv z hz hc
  haveI : CharZero O := charZero_of_injective_algebraMap (dvrFacts l O).1
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hlm : (l : O) ∈ maximalIdeal O := by
    haveI := (dvrFacts l O).2.2.1
    rw [← map_natCast (algebraMap ℤ_[l] O)]
    exact map_nonunit _ _ PadicInt.p_nonunit
  obtain ⟨B, hB⟩ := So.locKill lf lt le k Ω l O ψ ho n h0 h1 v A hA hv
  obtain ⟨g, hg, hne⟩ := So.decNe k Ω l O ψ ho n h0 v A hA
  obtain ⟨a, ha, m, hm⟩ := So.cobLim O (Dec (F := k) A) ((ψ * chiO k Ω l O ^ n).comp (Dec (F := k) A).subtype) l B hl0 hlm
    ⟨⟨g, hg⟩, hne⟩ (fun r => hB _ _ _ (isLev_lev (pow_ne_zero r hl0) _)) (fun g => z g) (fun g h => hz g h)
    fun N => (hc N).comp_continuous continuous_subtype_val
  exact ⟨a, ha, m, fun g hg => hm ⟨g, hg⟩ trivial⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCocL

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.soCocL : ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (ψ : G k Ω →* c.Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ e : ℕ, 1 ≤ e → ∀ z : G k Ω → c.O, Coc (Chr.Psi l e ψ)⁻¹ z → Alg.AdicCont (maximalIdeal c.O) z → (∀ v : HeightOneSpectrum (𝓞 k), ((l : ℕ) : 𝓞 k) ∈ v.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ CobOn (Chr.Psi l e ψ)⁻¹ z (Dec (F := k) A)) → CobOn (Chr.Psi l e ψ)⁻¹ z ⊤ := by
  intro CK hK pt fK tK lf lt le k Ω _ _ _ _ _ l hl c ψ ho e he z hz hc hl
  have key : ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v →
      CobOn (Chr.Psi l e ψ)⁻¹ z (Dec (F := k) A) := fun v A hA => by
    by_cases hv : ((l : ℕ) : 𝓞 k) ∈ v.asIdeal
    · obtain ⟨A', hA', h⟩ := hl v hv
      exact So.cobPlace k Ω c.O _ z hz v A' A hA' hA h
    · rw [Chr.Psi_inv] at hz ⊢
      have ho' : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
        have : (ψ⁻¹).ker = ψ.ker := by
          ext g
          simp [MonoidHom.mem_ker]
        rwa [this]
      exact So.locTors lf lt le k Ω l c.O ψ⁻¹ ho' _ (by omega) (by omega) v A hA hv z hz hc
  refine So.soCoc CK hK pt fK tK k Ω l c ψ ho e he z hz hc (fun A => ?_) fun A hA => ?_
  · by_cases h : A = ⊤
    · rw [((places k Ω l A).2.1 h).1]
      refine cobOn_of_eq_zero _ fun g hg => ?_
      rw [Subgroup.mem_bot.1 hg]
      simpa using hz 1 1
    · obtain ⟨v, hv⟩ := (places k Ω l A).1 h
      exact (key v A hv).mono (Ine_le_Dec A)
  · obtain ⟨v, hv⟩ := (places k Ω l A).1 fun h => ((places k Ω l A).2.1 h).2 hA
    exact key v A hv
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLineNeg

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem pl_uniq {l : ℕ} (hl : l.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have hp : Prime ((l : ℕ) : 𝓞 ℚ) := by
    have h : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl
    have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  have hm : (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero)
  exact HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))

theorem UpperTheory.V.X.So.lineNeg :
    ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (S : Finset UnitaryThreeInertia.Pl) (A : S → ValuationSubring Ω) (F : UnitaryThreeInertia.Frame c.O (G ℚ Ω) (UnitaryThreeInertia.Gam Ω S) S), 1 ≤ e → UnitaryThreeInertia.IsHostFrame Ω c e ψ S A F → ∀ j : ℤ, j < 0 → ∀ s : ℕ, LineVan F j (lineChar F j s) := by
  intro CK hK pt fK tK lf lt le Ω _ _ _ l hl c N _ e ψ S A F he hF j hj s z hz hc _ _ hD
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
  have hn : 1 ≤ n := by omega
  let η₀ : G ℚ Ω →* c.Oˣ := (Units.map (Int.castRingHom c.O).toMonoidHom).comp (UnitaryThreeInertia.eta4 Ω)
  let ψ' : G ℚ Ω →* c.Oˣ := Chr.dirG ℚ Ω ψ ^ n * (η₀ ^ s)⁻¹
  have hη : ∀ g, F.η (F.π g) = UnitaryThreeInertia.eta4 Ω g := fun g => DFunLike.congr_fun hF.η g
  have hΨ : ∀ g, F.Ψ (F.π g) = Chr.Psi l e (Chr.dirG ℚ Ω ψ) g := fun g => DFunLike.congr_fun hF.Ψ g
  have hθ : ∀ g, (Chr.Psi l (e * n) ψ')⁻¹ g = lineChar F (-(n : ℤ)) s (F.π g) := by
    intro g
    have h1 : etaO F (F.π g) = η₀ g := by
      simp only [etaO, η₀, MonoidHom.comp_apply, hη]
    simp only [lineChar, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, hΨ, h1,
      Chr.Psi, ψ', zpow_neg, zpow_natCast, mul_pow, pow_mul, mul_inv, inv_inv, mul_assoc]
  have ho : IsOpen (ψ'.ker : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker ⊓ (Chr.cls ℚ Ω 4).ker) (fun g hg => ?_)
      ((Chr.clsFacts ℚ Ω N).1.inter (Chr.clsFacts ℚ Ω 4).1)
    have h1 : Chr.cls ℚ Ω N g = 1 := hg.1
    have h2 : Chr.cls ℚ Ω 4 g = 1 := hg.2
    simp only [MonoidHom.mem_ker, ψ', η₀, UnitaryThreeInertia.eta4, Chr.dirG, MonoidHom.mul_apply, MonoidHom.pow_apply,
      MonoidHom.inv_apply, MonoidHom.comp_apply, h1, h2, map_one, one_pow, inv_one, mul_one]
  have hπc : Continuous F.π := by rw [hF.π]; exact continuous_toGS Ω _
  have hπs : Function.Surjective F.π := by rw [hF.π]; exact QuotientGroup.mk_surjective
  have hz' : Coc (Chr.Psi l (e * n) ψ')⁻¹ (fun g => z (F.π g)) := fun g h => by
    rw [hθ]
    show z (F.π (g * h)) = _
    rw [map_mul, hz]
  obtain ⟨a, ha, m, hm⟩ := So.soCocL CK hK pt fK tK lf lt le ℚ Ω l c ψ' ho (e * n) (Nat.mul_pos he hn)
    (fun g => z (F.π g)) hz' (fun k => (hc k).comp_continuous hπc) (fun v hv => by
      obtain rfl : v = F.vl.1 := pl_uniq hl.out hv hF.vl
      refine ⟨A F.vl, hF.isOver _, So.cobIndex c.O _ _ _ hz' (UnitaryThreeInertia.eta4 Ω).ker _ ?_ ?_⟩
      · haveI : (UnitaryThreeInertia.eta4 Ω).ker.FiniteIndex := ⟨by rw [Subgroup.index_ker]; exact Nat.card_pos.ne'⟩
        exact Subgroup.FiniteIndex.index_ne_zero
      · obtain ⟨y, hy⟩ := hD hj
        refine ⟨1, one_ne_zero, y, fun g hg => ?_⟩
        rw [one_mul, hθ]
        exact hy ⟨g, by rw [hF.D]; exact hg.2⟩ ((hη g).trans hg.1))
  refine ⟨a, ha, m, fun g _ => ?_⟩
  obtain ⟨g, rfl⟩ := hπs g
  rw [← hθ]
  exact hm g trivial
end
end
