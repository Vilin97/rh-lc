module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntForm
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsSmoothConeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationFunctionCellEqMinIntegralCombStatement
import Mathlib.Data.Finset.Functor

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportMinimisersLatticeAutomorphism

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory

theorem relabel_cong {N r : ℕ} (e : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) (x y : Fin r → ℤ)
    (h : ∀ i, ((x i : ℤ) : ZMod N) = y i) : ∀ i, ((e x i : ℤ) : ZMod N) = e y i := by
  have hd : ∀ i, (N : ℤ) ∣ x i - y i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h i).symm
  choose w hw using hd
  have hxy : x - y = (N : ℤ) • w := by ext i; simp [hw i]
  have he : e x - e y = (N : ℤ) • e w := by rw [← map_sub, hxy, map_smul]
  intro i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have := congrFun he i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  exact ⟨-(e w i), by linarith⟩

theorem qW_pull {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (f : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ))
    (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (y : Fin s → Fin r → ℤ) :
    qW W (pull f b) y = qW W b (fun u => f (y u)) := rfl

theorem relabel_minimisers : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (N : ℕ) [NeZero N] (r : ℕ) (μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ))), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∃ σ : Equiv.Perm (Fin 8 → Fin r → ZMod N), (∀ c u i, ((e.symm (μ (σ c) u) i : ℤ) : ZMod N) = c u i) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b') ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W (pull e.toLinearMap b') α) := by
  intro W N _ r μ hμ e
  have key : ∀ (f g : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)), (∀ x, g (f x) = x) → ∀ c u i,
      ((g (μ (fun u i => ((f (μ c u) i : ℤ) : ZMod N)) u) i : ℤ) : ZMod N) = c u i := by
    intro f g hgf c u i
    rw [relabel_cong g _ (f (μ c u)) (fun j => hμ _ u j) i, hgf, hμ]
  let σ : Equiv.Perm (Fin 8 → Fin r → ZMod N) :=
    { toFun := fun c u i => ((e (μ c u) i : ℤ) : ZMod N)
      invFun := fun c u i => ((e.symm (μ c u) i : ℤ) : ZMod N)
      left_inv := fun c => by
        funext u i
        exact key e.toLinearMap e.symm.toLinearMap (fun x => e.symm_apply_apply x) c u i
      right_inv := fun c => by
        funext u i
        exact key e.symm.toLinearMap e.toLinearMap (fun x => e.apply_symm_apply x) c u i }
  refine ⟨σ, fun c u i => key e.toLinearMap e.symm.toLinearMap (fun x => e.symm_apply_apply x) c u i, ?_⟩
  intro b' hmin c α hα
  rw [qW_pull, qW_pull]
  have h1 : (fun u => e.toLinearMap ((fun c u => e.symm (μ (σ c) u)) c u)) = μ (σ c) := by
    funext u; simp
  rw [h1]
  apply hmin (σ c) (fun u => e.toLinearMap (α u))
  intro u i
  show _ = ((e (μ c u) i : ℤ) : ZMod N)
  exact relabel_cong e.toLinearMap (α u) (μ c u) (fun j => (hα u j).trans (hμ c u j).symm) i

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportMinimisersLatticeAutomorphismStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_transport_minimisers_latticeAutomorphism : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (N : ℕ) [NeZero N] (r : ℕ) (μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ))), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∃ σ : Equiv.Perm (Fin 8 → Fin r → ZMod N), (∀ c u i, ((e.symm (μ (σ c) u) i : ℤ) : ZMod N) = c u i) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b') ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W (pull e.toLinearMap b') α) := by
  first | exact @GlobalTheory.relabel_minimisers | exact GlobalTheory.relabel_minimisers | (intros; apply GlobalTheory.relabel_minimisers <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntFormStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_pos_combination_smoothCone_symmIntForm : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) (cf : Fin m → ℕ), IsCone id φ γ ∧ (∀ j, 0 < cf j) ∧ b = ∑ j, cf j • γ j := by
  first | exact @GlobalTheory.ConeInterior.exists_pos_comb_int | exact GlobalTheory.ConeInterior.exists_pos_comb_int | (intros; apply GlobalTheory.ConeInterior.exists_pos_comb_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntBilinFormToRealMemPsdConeOfPos

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc

theorem toReal_mem_psdCone_of_pos_int : ∀ (r : ℕ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) →
    (∀ x, x ≠ 0 → 0 < b x x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) := by
  intro r b hs hp
  refine TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hs) fun y => ?_
  by_cases hy : y = 0
  · subst hy; simp
  · exact (hp y hy).le

end GlobalTheory.Poinc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntBilinFormToRealMemPsdConeOfPosStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.intBilinFormToReal_mem_psdCone_of_pos : ∀ (r : ℕ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) := by
  first | exact @GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | exact GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | (intros; apply GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsDefiniteFormsUpToAut

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.MinSysType

theorem finite_minimiser_systems_upTo_aut : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W →
    ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∃ S : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)),
    ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) →
    ∃ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∀ μ' : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)),
    (∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) →
    (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) →
      qW W (pull e.toLinearMap b) (μ' c) ≤ qW W (pull e.toLinearMap b) α) → μ' ∈ S := by
  intro g φ hφ W hW N _ hN r hr
  classical
  have hX : IsPolFanOn id φ (Fin r → ℤ) := hφ (Fin r → ℤ) (by simpa using hr)
  obtain ⟨S₀, hS₀, hfin⟩ := hX.finite
  set F := hS₀.toFinset with hF
  let ι := Σ m : Fin (F.card + 1), (Fin m.val → F)
  let P : ι → Prop := fun i => IsCone id φ (fun j => ((i.2 j : F) : LinearMap.BilinForm ℤ (Fin r → ℤ))) ∧
    ∀ x, x ≠ 0 → 0 < ∑ j, ((i.2 j : F) : LinearMap.BilinForm ℤ (Fin r → ℤ)) x x
  let T : ι → Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)) := fun i =>
    if h : P i then Classical.choose (GlobalTheory.T.finite_minimiser_systems_smooth_cone φ W hW N hN r i.1.val _ h.1 h.2) else ∅
  refine ⟨Finset.univ.biUnion T, ?_⟩
  intro b hsym hpos
  have hpsd := GlobalTheory.T.intBilinFormToReal_mem_psdCone_of_pos r b hsym hpos
  obtain ⟨m, γ, cf, hcone, hcf, hb⟩ := GlobalTheory.T.exists_pos_combination_smoothCone_symmIntForm g φ hφ r hr b hsym hpsd
  obtain ⟨e, he⟩ := hfin m γ hcone
  refine ⟨e, fun μ' h1 h2 => ?_⟩
  let γ' : Fin m → F := fun j => ⟨pull e.toLinearMap (γ j), hS₀.mem_toFinset.2 (he j)⟩
  have hcone' := hcone.pull_equiv e
  have hinj : Function.Injective γ' := fun j k hjk => by
    have h := congrArg Subtype.val hjk
    simp only [γ'] at h
    exact hcone'.injective h
  have hm : m < F.card + 1 := by
    have := Fintype.card_le_of_injective γ' hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  let i : ι := ⟨⟨m, hm⟩, γ'⟩
  have hbyy : ∀ y, b y y = ∑ j, (cf j : ℤ) * γ j y y := fun y => by
    rw [hb]; simp [LinearMap.sum_apply]
  have hPi : P i := by
    refine ⟨hcone', fun x hx => ?_⟩
    simp only [i, γ', pull_apply]
    have hex : e x ≠ 0 := by simpa using hx
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ γ j (e x) (e x) := fun j _ => hcone.nonneg j _
    refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => ?_
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
    have := hpos _ hex
    rw [hbyy] at this
    simp [hz] at this
  have hmem : μ' ∈ T i := by
    simp only [T, dif_pos hPi]
    refine Classical.choose_spec (GlobalTheory.T.finite_minimiser_systems_smooth_cone φ W hW N hN r i.1.val _ hPi.1 hPi.2) (pull e.toLinearMap b) 1 cf
      one_pos hcf ?_ μ' h1 h2
    ext a c
    simp [i, γ', pull_apply, hb, LinearMap.sum_apply]
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hmem⟩

end GlobalTheory.Poinc.MinSysType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsDefiniteFormsUpToAutStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.finite_minimiser_systems_definite_forms_upTo_aut : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∃ S : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∃ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∀ μ' : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b) (μ' c) ≤ qW W (pull e.toLinearMap b) α) → μ' ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut | exact GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut | (intros; apply GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimiserCellFunctionMinFinitelyManyCombinations

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem GlobalTheory.Poinc.finite_types : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∃ (ι : ℕ) (𝓛 : Finset (Finset ((Fin 8 → Fin r → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → ∃ L ∈ 𝓛, ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  intro g φ hφ W hW N _ hN hε r hr
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_minimiser_systems_definite_forms_upTo_aut g φ hφ W hW N hN r hr
  have hP : ∀ μ' : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ),
      ((∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) ∧ ∃ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ),
        (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ' c) ≤ qW W b₀ α)) →
      ∃ (ι : ℕ) (L : Finset ((Fin 8 → Fin r → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)),
        (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) →
        (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ' c) ≤ qW W b' α) →
        (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ' c)) ∧
          ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ' c) :=
    fun μ' ⟨h1, b₀, h2, h3, h4⟩ => GlobalTheory.T.polarisationFunction_cell_eq_min_integral_comb g φ hφ W hW N hN hε r hr μ' h1 b₀ h2 h3 h4
  choose! ιf Lf hιf hLf using hP
  set ι : ℕ := ∏ μ' ∈ S, max (ιf μ') 1 with hιdef
  refine ⟨ι, S.biUnion fun μ' => Finset.univ.image fun σ : Equiv.Perm (Fin 8 → Fin r → ZMod N) =>
    (Lf μ').image fun ν c => ((ι / ιf μ' : ℕ) : ℤ) * ν (σ c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => by omega)
  intro b hbs hbp μ hμ hmin
  obtain ⟨e, he⟩ := hS b hbs hbp
  obtain ⟨σ, hσ1, hσ2⟩ := GlobalTheory.T.exists_transport_minimisers_latticeAutomorphism W N r μ hμ e
  have hpd : ∀ x, x ≠ 0 → 0 < pull e.toLinearMap b x x := fun x hx => by
    simpa using hbp (e x) (by simpa using hx)
  have hPμ := And.intro hσ1 (⟨pull e.toLinearMap b, fun x y => hbs _ _, hpd, hσ2 b hmin⟩ :
    ∃ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
      (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) →
        qW W b₀ ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W b₀ α))
  have hmem := he _ hσ1 (hσ2 b hmin)
  have hι1 := hιf _ hPμ
  have hL := hLf _ hPμ
  set μ' : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ) := fun c u => e.symm (μ (σ c) u) with hμ'
  have hdvd : ιf μ' ∣ ι := by
    have := Finset.dvd_prod_of_mem (fun μ'' => max (ιf μ'') 1) hmem
    simpa [max_eq_left hι1] using this
  set k : ℕ := ι / ιf μ' with hk
  have hkι : (ι : ℝ) = k * ιf μ' := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  refine ⟨(Lf μ').image fun ν c => ((k : ℕ) : ℤ) * ν (σ.symm c),
    Finset.mem_biUnion.2 ⟨μ', hmem, Finset.mem_image.2 ⟨σ.symm, Finset.mem_univ _, rfl⟩⟩, ?_⟩
  intro b' hb's hb'p hb'min
  have key := hL (pull e.toLinearMap b') (fun x y => hb's _ _) (fun x => hb'p _) (hσ2 b' hb'min)
  have hφ' : φ.evalZ (pull e.toLinearMap b') = φ.evalZ b' := evalZ_pull φ e.surjective b'
  have hq : ∀ c, qW W (pull e.toLinearMap b') (μ' c) = qW W b' (μ (σ c)) := fun c => by
    simp [qW, μ']
  have hsum : ∀ ν : (Fin 8 → Fin r → ZMod N) → ℤ,
      ∑ c, ((((k : ℕ) : ℤ) * ν (σ.symm c) : ℤ) : ℝ) * qW W b' (μ c) =
        k * ∑ c, (ν c : ℝ) * qW W (pull e.toLinearMap b') (μ' c) := fun ν => by
    rw [Finset.mul_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hq]; simp; ring
  have hlhs : (ι * N : ℝ) * φ.evalZ b' = k * ((ιf μ' * N : ℝ) * φ.evalZ (pull e.toLinearMap b')) := by
    rw [hφ', hkι]; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
    rw [hsum, hlhs]
    exact mul_le_mul_of_nonneg_left (key.1 ν hν) hk0
  · obtain ⟨ν, hν, heq⟩ := key.2
    exact ⟨_, Finset.mem_image_of_mem _ hν, by rw [hsum, hlhs, heq]⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimiserCellFunctionMinFinitelyManyCombinationsStatement

section

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.minimiser_cell_function_min_finitely_many_combinations : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∃ (ι : ℕ) (𝓛 : Finset (Finset ((Fin 8 → Fin r → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → ∃ L ∈ 𝓛, ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  first | exact @GlobalTheory.Poinc.finite_types | exact GlobalTheory.Poinc.finite_types | (intros; apply GlobalTheory.Poinc.finite_types <;> assumption)
end
end
