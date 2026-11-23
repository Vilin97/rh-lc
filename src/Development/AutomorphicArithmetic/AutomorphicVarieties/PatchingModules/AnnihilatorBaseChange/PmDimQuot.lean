module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Mathlib.RingTheory.Regular.RegularSequence
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
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
public import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplModfree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.YPrime
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDepthCat

section

@[expose] public section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.exists_isRegular_of_free_quotient :
    ∀ (L B : Type) [CommRing L] [IsRegularLocalRing L] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra L B] [IsLocalHom (algebraMap L B)] (M : Type) [AddCommGroup M] [Module B M] [Module L M]
      [IsScalarTower L B M] [Module.Finite B M] [Nontrivial M] (r e : ℕ) (y : Fin r → B),
      ringKrullDim L = e → (∀ i, y i ∈ maximalIdeal B) → GlobalTheory.IsQuasiRegularSeq M y →
      Module.Free L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      ∃ xs : List B, xs.length = r + e ∧ (∀ x ∈ xs, x ∈ maximalIdeal B) ∧ RingTheory.Sequence.IsRegular M xs := by
  intro L B _ _ _ _ _ _ _ M _ _ _ _ _ _ r e y he hy hq hfree
  obtain ⟨zs, h, hd⟩ := GlobalTheory.exists_ofList_eq_maximalIdeal_length_eq L
  have hreg := (GlobalTheory.isRegular_of_ofList_eq_maximalIdeal h hd.le).toIsWeaklyRegular
  have hlen : zs.length = e := by
    rw [he] at hd
    exact_mod_cast hd
  have hmem : ∀ x ∈ List.ofFn y ++ zs.map (algebraMap L B), x ∈ maximalIdeal B := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hy i
    · refine map_maximalIdeal_le (algebraMap L B) ?_
      rw [← h, Ideal.map_ofList]
      exact Ideal.subset_span hx
  refine ⟨List.ofFn y ++ zs.map (algebraMap L B), by simp [hlen], hmem, ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem,
    RingTheory.Sequence.isWeaklyRegular_append_iff, GlobalTheory.ofList_ofFn_eq_span_range,
    RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff]
  refine ⟨hq.isWeaklyRegular ?_, ?_⟩
  · exact fun i => maximalIdeal_le_jacobson _ (hy i)
  · exact ((TensorProduct.lid L _).isWeaklyRegular_congr zs).mp hreg.isWeaklyRegular_rTensor
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDimFin

section

@[expose] public section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.supportDim_le_of_finite :
    ∀ (L B : Type) [CommRing L] [IsNoetherianRing L] [CommRing B] [Algebra L B] (N : Type) [AddCommGroup N] [Module B N]
      [Module L N] [IsScalarTower L B N] [Module.Finite L N], Module.supportDim B N ≤ ringKrullDim L := by
  intro L B _ _ _ _ N _ _ _ _ _
  have hfin : Module.Finite B N := Module.Finite.of_restrictScalars_finite L B N
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  let f : B →ₐ[L] Module.End L N := Algebra.lsmul L L N
  have hf : ∀ b : B, b ∈ Module.annihilator B N → f b = 0 := by
    intro b hb
    ext n
    exact Module.mem_annihilator.mp hb n
  let g : (B ⧸ Module.annihilator B N) →ₐ[L] Module.End L N :=
    Ideal.Quotient.liftₐ (Module.annihilator B N) f hf
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).mpr ?_
    intro q hq
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine Module.mem_annihilator.mpr (fun n => ?_)
    have h := LinearMap.congr_fun hq n
    exact h
  haveI : Algebra.IsIntegral L (B ⧸ Module.annihilator B N) :=
    ⟨fun q => (isIntegral_algHom_iff g hinj).mp (Algebra.IsIntegral.isIntegral _)⟩
  exact Order.krullDim_le_of_strictMono
    (fun P => (⟨Ideal.comap (algebraMap L (B ⧸ Module.annihilator B N)) P.asIdeal, inferInstance⟩ :
      PrimeSpectrum L))
    (fun P Q h => Ideal.IsIntegral.comap_lt_comap h)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaEquidim

section

@[expose] public section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.dim_minimalPrime_eq :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (M : Type) [AddCommGroup M] [Module B M]
      [Module.Finite B M] (xs : List B), (∀ x ∈ xs, x ∈ maximalIdeal B) → RingTheory.Sequence.IsWeaklyRegular M xs →
      Module.supportDim B M ≤ (xs.length : ℕ) →
      ∀ Z ∈ (Module.annihilator B M).minimalPrimes, ringKrullDim (B ⧸ Z) = (xs.length : ℕ) := by
  intro B _ _ _ M _ _ _ xs hxs hreg hdim Z hZ
  apply le_antisymm
  · calc ringKrullDim (B ⧸ Z) ≤ ringKrullDim (B ⧸ Module.annihilator B M) :=
          ringKrullDim_le_of_surjective (Ideal.Quotient.factor hZ.1.2)
            (Ideal.Quotient.factor_surjective hZ.1.2)
      _ = Module.supportDim B M := (Module.supportDim_eq_ringKrullDim_quotient_annihilator B M).symm
      _ ≤ _ := hdim
  · exact GlobalTheory.length_le_ringKrullDim_quotient_of_isAssociatedPrime hxs hreg
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B M hZ)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCmPatch

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.patched_depth_dim :
    ∀ (L B : Type) [CommRing L] [IsRegularLocalRing L] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra L B] [IsLocalHom (algebraMap L B)] (M : Type) [AddCommGroup M] [Module B M] [Module L M]
      [IsScalarTower L B M] [Module.Finite B M] [Nontrivial M] (r e : ℕ) (y : Fin r → B),
      ringKrullDim L = e → (∀ i, y i ∈ maximalIdeal B) → GlobalTheory.IsQuasiRegularSeq M y →
      Module.Free L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      Module.Finite L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      (∃ xs : List B, xs.length = r + e ∧ (∀ x ∈ xs, x ∈ maximalIdeal B) ∧ RingTheory.Sequence.IsRegular M xs) ∧
      ∀ Z ∈ (Module.annihilator B M).minimalPrimes, ringKrullDim (B ⧸ Z) = ((r + e : ℕ) : WithBot ℕ∞) := by
  intro L B _ _ _ _ _ _ _ M _ _ _ _ _ _ r e y hL hy hq hfree hfin
  refine ⟨exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree, ?_⟩
  obtain ⟨xs, hlen, hxs, hreg⟩ := exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree
  have hys : ∀ z ∈ List.ofFn y, z ∈ maximalIdeal B := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hy i
  have h1 := GlobalTheory.supportDim_le_supportDim_quotient_add_length (M := M) hys
  rw [GlobalTheory.ofList_ofFn_eq_span_range, List.length_ofFn] at h1
  have h2 := supportDim_le_of_finite L B (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M))
  rw [hL] at h2
  have hdim : Module.supportDim B M ≤ ((xs.length : ℕ) : WithBot ℕ∞) := by
    refine h1.trans ?_
    rw [hlen]
    calc Module.supportDim B (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) + ((r : ℕ) : WithBot ℕ∞)
        ≤ ((e : ℕ) : WithBot ℕ∞) + ((r : ℕ) : WithBot ℕ∞) := by gcongr
      _ = ((r + e : ℕ) : WithBot ℕ∞) := by
        rw [add_comm]; norm_cast
  intro Z hZ
  have := dim_minimalPrime_eq B M xs hxs hreg.toIsWeaklyRegular hdim Z hZ
  rw [this, hlen]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmDimQuot

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem pmDim_quot {A B σ M : Type} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module A M] (y : σ → A) :
    Nonempty (((B ⊗[A] M) ⧸ (Ideal.span (Set.range fun i => algebraMap A B (y i)) • ⊤ :
      Submodule B (B ⊗[A] M))) ≃ₗ[B] B ⊗[A] (M ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule A M))) := by
  classical
  set I : Ideal A := Ideal.span (Set.range y) with hIdef
  have hI : Ideal.span (Set.range fun i => algebraMap A B (y i)) = I.map (algebraMap A B) := by
    rw [hIdef, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hI]
  refine ⟨(TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := A) B A B
    (I • ⊤ : Submodule A M) ≪≫ₗ Submodule.quotEquivOfEq _ _ ?_).symm⟩
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      obtain ⟨m, hm⟩ := m
      simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
        Submodule.coe_subtype]
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro a ha m' _
        rw [← TensorProduct.smul_tmul, algebra_compatible_smul B a, ← TensorProduct.smul_tmul']
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
      · intro u v hu hv
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hu hv
    | add x z hx hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hz
  · rw [Submodule.smul_le]
    intro r hr x hx
    clear hx
    induction hr using Submodule.span_induction generalizing x with
    | mem r hr =>
      obtain ⟨a, ha, rfl⟩ := hr
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b m =>
        refine ⟨b ⊗ₜ[A] (⟨a • m, Submodule.smul_mem_smul ha Submodule.mem_top⟩ : (I • ⊤ : Submodule A M)), ?_⟩
        simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
          Submodule.coe_subtype]
        rw [← TensorProduct.smul_tmul, algebra_compatible_smul B a, TensorProduct.smul_tmul']
      | add u v hu hv =>
        rw [smul_add]
        exact Submodule.add_mem _ hu hv
    | zero => simp
    | add r s _ _ hr hs =>
      rw [add_smul]
      exact Submodule.add_mem _ (hr x) (hs x)
    | smul c r _ hr =>
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ c (hr x)

private theorem pmDim_step {L B σ M N : Type} [CommRing L] [IsRegularLocalRing L] [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [Algebra L B] [IsLocalHom (algebraMap L B)] [Fintype σ]
    [AddCommGroup M] [Module B M] [Module.Finite B M] [AddCommGroup N] [Module B N] [Module L N]
    [IsScalarTower L B N] [Module.Free L N] [Module.Finite L N] (d : ℕ) (y : σ → B)
    (hd : ringKrullDim L = d) (hy : ∀ i, y i ∈ maximalIdeal B) (hq : GlobalTheory.IsQuasiRegularSeq M y)
    (e : (M ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule B M)) ≃ₗ[B] N) :
    ∀ Z ∈ (Module.annihilator B M).minimalPrimes,
      ringKrullDim (B ⧸ Z) = ((d + Fintype.card σ : ℕ) : WithBot ℕ∞) := by
  classical
  intro Z hZ
  rcases subsingleton_or_nontrivial M with hM | hM
  · have htop : Module.annihilator B M = ⊤ := Module.annihilator_eq_top_iff.mpr hM
    rw [htop] at hZ
    exact absurd (top_le_iff.mp hZ.1.2) hZ.1.1.ne_top
  · letI : Module L M := Module.compHom M (algebraMap L B)
    haveI : IsScalarTower L B M := ⟨fun a b m => by
      show (a • b) • m = algebraMap L B a • (b • m)
      rw [Algebra.smul_def, mul_smul]⟩
    let eσ : Fin (Fintype.card σ) ≃ σ := (Fintype.equivFin σ).symm
    have hq' := hq.comp_equiv eσ
    have hspan : Ideal.span (Set.range (y ∘ eσ)) = Ideal.span (Set.range y) := by
      rw [Set.range_comp, EquivLike.range_eq_univ, Set.image_univ]
    let e' : (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) ≃ₗ[L] N :=
      ((Submodule.quotEquivOfEq _ _ (by rw [hspan])) ≪≫ₗ e).restrictScalars L
    have hfree : Module.Free L (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) :=
      Module.Free.of_equiv e'.symm
    have hfin : Module.Finite L (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) :=
      Module.Finite.equiv e'.symm
    have h := (UpperTheory.V.AlgebraTools.patched_depth_dim L B M (Fintype.card σ) d (y ∘ eσ) hd
      (fun i => hy _) hq' hfree hfin).2 Z hZ
    rw [h, Nat.add_comm]

theorem UpperTheory.V.Pa.Core.pmDim :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [IsNoetherianRing R] [Fintype σ] (c : Λ →+* R) (y : σ → R) (f : R) (ii : Ideal R) (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Free Λ X] [Module.Finite Λ X] (P : PMod y f ii X) (q : Ideal R) (d : ℕ) (La B : Type) [CommRing La] [IsLocalRing La] [Algebra Λ La] [CommRing B] [IsLocalRing B] [Algebra P.BB B], (∀ (a : Λ) (x : X), a • x = c a • x) → q.IsPrime → f ∉ q → (∀ a, y a ∈ q) → IsCplAt Λ (q.comap c) La → IsRegularLocalRing La → ringKrullDim La = d → IsCplAt P.BB (q.map (algebraMap R P.BB)) B → ∀ Z ∈ (Module.annihilator B (B ⊗[P.BB] P.MM)).minimalPrimes, ringKrullDim (B ⧸ Z) = ((d + Fintype.card σ : ℕ) : WithBot ℕ∞) := by
  intro Λ R σ _ _ _ _ _ c y f ii X _ _ _ _ _ P q d La B _ _ _ _ _ _ hc hq hf hy hLa hreg hdim hB
  classical
  have hYP := UpperTheory.V.Pa.Core.yPrime R σ y f P.BB P.cpl q hq hf hy
  haveI : IsNoetherianRing P.BB := P.cpl.noeth
  haveI : IsNoetherianRing B := hB.noeth
  haveI : Module.Finite P.BB P.MM := P.fin
  haveI : IsAdicComplete (maximalIdeal B) B := hB.complete
  letI : Algebra R B := ((algebraMap P.BB B).comp (algebraMap R P.BB)).toAlgebra
  haveI : IsScalarTower R P.BB B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRB : IsCplAt R q B := hYP.2.2.2 B hB
  haveI : Module.Flat P.BB B := UpperTheory.V.AlgebraTools.IsCplAt.flat P.BB _ B hB
  let φ : Λ →+* B := (algebraMap R B).comp c
  have hφ : Ideal.comap φ (maximalIdeal B) = q.comap c := by
    show Ideal.comap ((algebraMap P.BB B).comp ((algebraMap R P.BB).comp c)) (maximalIdeal B) = q.comap c
    rw [← Ideal.comap_comap, ← Ideal.comap_comap, hB.comap_eq, hYP.2.1]
  obtain ⟨ψ, hψ, -⟩ := UpperTheory.V.AlgebraTools.IsCplAt.existsUnique_lift Λ (q.comap c) La hLa B φ hφ
  letI : Algebra La B := ψ.toAlgebra
  haveI : IsLocalHom (algebraMap La B) := by
    show IsLocalHom ψ
    refine ((IsLocalRing.local_hom_tfae ψ).out 1 4).mpr ?_
    have hm : maximalIdeal La = (q.comap c).map (algebraMap Λ La) := by
      simpa using (UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq Λ (q.comap c) La hLa 1).symm
    rw [hm, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hψ, hφ]
  letI : Algebra Λ R := c.toAlgebra
  letI : Algebra Λ B := φ.toAlgebra
  haveI : IsScalarTower Λ R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Λ La B :=
    IsScalarTower.of_algebraMap_eq (fun x => (RingHom.congr_fun hψ x).symm)
  haveI : IsScalarTower Λ R X := ⟨fun a r x => by
    show (c a * r) • x = a • (r • x)
    rw [mul_smul, hc]⟩
  obtain ⟨hfin, hfree⟩ :=
    UpperTheory.V.AlgebraTools.IsCplAt.finite_free_baseChange Λ R (q.comap c) q La B X hLa hRB rfl
  haveI := hfin
  haveI := hfree
  let y' : σ → B := fun i => algebraMap P.BB B (algebraMap R P.BB (y i))
  obtain ⟨e1⟩ := pmDim_quot (A := P.BB) (B := B) (M := P.MM) (fun a => algebraMap R P.BB (y a))
  let e : ((B ⊗[P.BB] P.MM) ⧸ (Ideal.span (Set.range y') • ⊤ : Submodule B (B ⊗[P.BB] P.MM))) ≃ₗ[B]
      B ⊗[R] X :=
    e1 ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) P.fib ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R P.BB B B X
  have hy' : ∀ i, y' i ∈ maximalIdeal B := by
    intro i
    have h : algebraMap R P.BB (y i) ∈ Ideal.comap (algebraMap P.BB B) (maximalIdeal B) := by
      rw [hB.comap_eq]
      exact Ideal.mem_map_of_mem _ (hy i)
    exact h
  have hqr : GlobalTheory.IsQuasiRegularSeq (B ⊗[P.BB] P.MM) y' := P.qr.baseChange B
  exact pmDim_step (L := La) (B := B) (M := B ⊗[P.BB] P.MM) (N := B ⊗[R] X) d y' hdim hy' hqr e
end
end
