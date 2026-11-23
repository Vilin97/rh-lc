module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenomNotMemOfPrInt
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitComponentIntegerResidueZeroIffMemPrime
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColCond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitComponentIntegerResidueZeroIffMemPrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

theorem _root_.GlobalTheory.T.split_component_integer_residue_zero_iff_mem_prime : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ c : 𝓞 D.host.E,
    ∃ h : p.pr (incA D (algebraMap (𝓞 D.host.E) D.host.E c)) ∈ 𝒪[k], (residue 𝒪[k] ⟨_, h⟩ = 0 ↔ c ∈ P.asIdeal) := by
  first | exact @GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff | exact GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff | (intros; apply GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLatticeComponentIntegralFrameCoords

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal.LatChar

variable {D : D7}

theorem finPart_pair_zero (α : Af D.host.F) (x : D.host.E) :
    finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = α ⊗ₜ[D.host.F] x := rfl

theorem latV_int {S : HSp D} {L : Lat S} (hL : ∀ z ∈ L, z ∈ intVec D S.rank) {P : Pl D → Prop}
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) (i : Fin S.rank) : finPart D (y i) ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    change finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) ∈ intAE D
    rw [finPart_pair_zero, one_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, ⟨x i, hL x hx i⟩, rfl⟩
  | zero => rw [Pi.zero_apply, RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Pi.add_apply, RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [Pi.neg_apply, RingHom.map_neg]; exact neg_mem hx

theorem lat_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
    {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)),
    β.IsLat L Λ → (∀ z, z ∈ L ↔ z ∈ intVec D _) → ∀ x : n → k, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := by
  intro D k _ _ _ _ p S n _ _ β L Λ hΛ hL x
  rw [hΛ x]
  constructor
  · intro h r
    exact (p.int_iff _).2 (latV_int (fun z hz => (hL z).1 hz) h r)
  · intro h
    have h1 : (fun i => p.sec ((β.b *ᵥ x) i)) =
        ∑ r, fun i => p.sec ((β.b *ᵥ x) r) * incA D ((Pi.single r 1 : Fin S.rank → D.host.E) i) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, RingHom.map_one, mul_one]
      · intro r _ hr
        rw [Pi.single_eq_of_ne hr.symm, RingHom.map_zero, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [h1]
    refine sum_mem fun r _ => GlobalTheory.FinPl.FrameLat.int_mul_mem (GlobalTheory.FinPl.FrameLat.sec_mem_intAt p _ (h r)) ((hL _).2 fun i => ?_)
    by_cases hi : i = r
    · subst hi; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne hi]; exact isIntegral_zero

end GlobalTheory.PhiOneVal.LatChar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLatticeComponentIntegralFrameCoordsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

theorem _root_.GlobalTheory.T.split_place_lattice_component_integral_frame_coords : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
    {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)),
    β.IsLat L Λ → (∀ z, z ∈ L ↔ z ∈ intVec D _) → ∀ x : n → k, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := by
  first | exact @GlobalTheory.PhiOneVal.LatChar.lat_iff | exact GlobalTheory.PhiOneVal.LatChar.lat_iff | (intros; apply GlobalTheory.PhiOneVal.LatChar.lat_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLevelPrimePhiOneEqOneIffColumns

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section
namespace GlobalTheory.PhiOneVal

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_last_of_pair {a : ℕ} (Q : Pair k (Fin a)) : ∃ r : Fin a, r.1 + 1 = a := by
  rcases a with _ | a
  · exact absurd (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]) Q.fn_ne
  · exact ⟨Fin.last a, rfl⟩

theorem hasVal_finset_sum {n ι : Type} (Q : Pair k n) (s : Finset ι) (x : ι → n → k) (v : ι → 𝓀[k])
    (h : ∀ i, Q.HasVal (x i) (v i)) : Q.HasVal (∑ i ∈ s, x i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Pair.mem_ker.1 (zero_mem Q.ker)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i).add ih

theorem maps_iff_basis {n n' : Type} [Fintype n] [DecidableEq n] (Q : Pair k n) (Q' : Pair k n') (A A' : Matrix n n k)
    (hA : A' * A = 1) (hQ : ∀ x ∈ Q.lat, ∀ r, (A *ᵥ x) r ∈ 𝒪[k]) (v : n → 𝓀[k])
    (hv : ∀ r, Q.HasVal (A' *ᵥ Pi.single r 1) (v r)) (M : Matrix n' n k) :
    Maps Q Q' M ↔ ∀ r, Q'.HasVal (M *ᵥ (A' *ᵥ Pi.single r 1)) (v r) := by
  rw [maps_iff_hasVal]
  refine ⟨fun h r => h _ _ (hv r), fun h y c hy => ?_⟩
  let w : n → 𝒪[k] := fun r => ⟨_, hQ y hy.mem r⟩
  have e : y = ∑ r, w r • (A' *ᵥ Pi.single r 1) := by
    have e1 : A *ᵥ y = ∑ r, w r • (Pi.single r 1 : n → k) := by
      ext i
      simp [w, Pi.single_apply, Finset.sum_apply, Subring.smul_def]
    calc y = A' *ᵥ (A *ᵥ y) := by rw [mulVec_mulVec, hA, one_mulVec]
      _ = _ := by
        rw [e1, mulVec_sum]
        exact Finset.sum_congr rfl fun r _ => mulVec_smul _ _ _
  have h1 := hasVal_finset_sum Q Finset.univ _ _ fun r => (hv r).smul (w r)
  have h2 := hasVal_finset_sum Q' Finset.univ _ _ fun r => (h r).smul (w r)
  rw [← e] at h1
  rw [hy.unique h1]
  convert h2 using 1
  conv_lhs => rw [e, mulVec_sum]
  exact Finset.sum_congr rfl fun r _ => mulVec_smul _ _ _

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (φ : E →+* k) (ψ : 𝓞 E →+* 𝒪[k])

theorem hasVal_col_iff (hψ : ∀ c, (ψ c : k) = φ (algebraMap (𝓞 E) E c))
    (hres : ∀ c, residue 𝒪[k] (ψ c) = 0 ↔ c ∈ P.asIdeal)
    (hint : ∀ x : E, φ x ∈ 𝒪[k] → ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E s * x)
    {b : ℕ} (Q : Pair k (Fin b)) (B B' : Matrix (Fin b) (Fin b) k) (hB : B * B' = 1)
    (hQ : ∀ x ∈ Q.lat, ∀ r, (B *ᵥ x) r ∈ 𝒪[k]) (t : 𝓞 E)
    (hv : ∀ w : Fin b → 𝓞 E, ∀ r : Fin b, r.1 + 1 = b →
      Q.HasVal (B' *ᵥ fun r' => φ (algebraMap (𝓞 E) E (w r'))) (residue 𝒪[k] (ψ (t * w r))))
    (u : Fin b → E) (ε : 𝓞 E) :
    Q.HasVal (B' *ᵥ fun q => φ (u q)) (residue 𝒪[k] (ψ (t * ε))) ↔
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : Fin b → 𝓞 E, (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * u q) ∧
        ∀ q : Fin b, q.1 + 1 = b → t * (c q - s * ε) ∈ P.asIdeal := by
  have key : ∀ (s : 𝓞 E) (c : Fin b → 𝓞 E), (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * u q) →
      (B' *ᵥ fun r' => φ (algebraMap (𝓞 E) E (c r'))) = ψ s • (B' *ᵥ fun q => φ (u q)) := by
    intro s c hc
    rw [← mulVec_smul]
    congr 1
    ext q
    rw [hc, map_mul, ← hψ]
    rfl
  have key2 : ∀ s c : 𝓞 E, t * (c - s * ε) ∈ P.asIdeal ↔
      residue 𝒪[k] (ψ (t * c)) = residue 𝒪[k] (ψ s) * residue 𝒪[k] (ψ (t * ε)) := by
    intro s c
    rw [← hres, ← map_mul, ← map_mul, show t * (c - s * ε) = t * c - s * (t * ε) by ring, map_sub, map_sub, sub_eq_zero]
  constructor
  · intro h
    have h1 := hQ _ h.mem
    rw [mulVec_mulVec, hB, one_mulVec] at h1
    choose s hs c hc using fun q => hint _ (h1 q)
    have hc' : ∀ q, algebraMap (𝓞 E) E (c q * ∏ q' ∈ Finset.univ.erase q, s q') =
        algebraMap (𝓞 E) E (∏ q', s q') * u q := by
      intro q
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ q), map_mul, map_mul, hc]
      ring
    refine ⟨∏ q, s q, ?_, fun q => c q * ∏ q' ∈ Finset.univ.erase q, s q', hc', fun q hq => ?_⟩
    · haveI := P.isPrime
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨q, -, hq⟩
      exact hs q hq
    · rw [key2]
      have h2 := hv (fun q => c q * ∏ q' ∈ Finset.univ.erase q, s q') q hq
      rw [key _ _ hc'] at h2
      exact h2.unique (h.smul _)
  · rintro ⟨s, hs, c, hc, hP⟩
    obtain ⟨q, hq⟩ := exists_last_of_pair Q
    have h2 := hv c q hq
    rw [key _ _ hc, (key2 _ _).1 (hP q hq)] at h2
    obtain ⟨v, hv'⟩ : IsUnit (ψ s) := by
      by_contra hn
      exact hs ((hres s).1 ((residue_eq_zero_iff _).2 hn))
    have h3 := h2.smul (↑v⁻¹ : 𝒪[k])
    rwa [← hv', smul_smul, Units.inv_mul, one_smul, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h3

end Local

theorem maps_rd_iff_colCond : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P →
    ∀ {S T : HSp D} {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (α : Frame p S (Fin S.rank)) (β : Frame p T (Fin T.rank))
    (Q : Pair k (Fin S.rank)) (Q' : Pair k (Fin T.rank)) (LS : Lat S) (LT : Lat T) (t : 𝓞 D.host.E),
    (∀ z, z ∈ LS ↔ z ∈ intVec D _) → (∀ z, z ∈ LT ↔ z ∈ intVec D _) → α.IsLat LS Q.lat → β.IsLat LT Q'.lat →
    (∀ w ∈ LS, ∀ r : Fin S.rank, r.1 + 1 = S.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q.HasVal (α.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    (∀ w ∈ LT, ∀ r : Fin T.rank, r.1 + 1 = T.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q'.HasVal (β.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (Maps Q Q' (GlobalTheory.FinPl.rd α β (z.map (incA D))) ↔ ColCond P t (toHom S T hS hT z)) := by
  intro D k _ _ _ _ p P hP S T a b hS hT α β Q Q' LS LT t hLS hLT hα hβ vS vT z
  subst hS hT
  let φ : D.host.E →+* k := p.pr.comp (incA D)
  have hres := GlobalTheory.T.split_component_integer_residue_zero_iff_mem_prime p P hP
  let ψ : 𝓞 D.host.E →+* 𝒪[k] := (φ.comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict _ fun c => (hres c).1
  have hψ : ∀ c, (ψ c : k) = φ (algebraMap (𝓞 D.host.E) D.host.E c) := fun c => rfl
  have hres' : ∀ c, residue 𝒪[k] (ψ c) = 0 ↔ c ∈ P.asIdeal := fun c => (hres c).2
  have hS : ∀ w : Fin S.rank → 𝓞 D.host.E, ∀ r : Fin S.rank, r.1 + 1 = S.rank →
      Q.HasVal (α.b' *ᵥ fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E (w r'))) (residue 𝒪[k] (ψ (t * w r))) := by
    intro w r hr
    obtain ⟨s, hs, h⟩ := vS (fun r' => algebraMap (𝓞 D.host.E) D.host.E (w r')) ((hLS _).2 fun i => (w i).isIntegral_coe) r hr
    have : s = ψ (t * w r) := Subtype.ext (by rw [hs, hψ, map_mul (algebraMap (𝓞 D.host.E) D.host.E)]; rfl)
    exact this ▸ h
  have hT : ∀ w : Fin T.rank → 𝓞 D.host.E, ∀ r : Fin T.rank, r.1 + 1 = T.rank →
      Q'.HasVal (β.b' *ᵥ fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E (w r'))) (residue 𝒪[k] (ψ (t * w r))) := by
    intro w r hr
    obtain ⟨s, hs, h⟩ := vT (fun r' => algebraMap (𝓞 D.host.E) D.host.E (w r')) ((hLT _).2 fun i => (w i).isIntegral_coe) r hr
    have : s = ψ (t * w r) := Subtype.ext (by rw [hs, hψ, map_mul (algebraMap (𝓞 D.host.E) D.host.E)]; rfl)
    exact this ▸ h
  obtain ⟨l, hl⟩ := exists_last_of_pair Q
  have hy : ∀ r : Fin S.rank, Q.HasVal (α.b' *ᵥ Pi.single r 1)
      (residue 𝒪[k] (ψ (t * if r.1 + 1 = S.rank then 1 else 0))) := by
    intro r
    have h := hS (Pi.single r 1) l hl
    have e1 : (fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E ((Pi.single r 1 : Fin S.rank → 𝓞 D.host.E) r'))) =
        Pi.single r 1 := by
      ext r'
      by_cases h' : r' = r <;> simp [Pi.single_apply, h']
    have e2 : (Pi.single r 1 : Fin S.rank → 𝓞 D.host.E) l = if r.1 + 1 = S.rank then 1 else 0 := by
      rw [Pi.single_apply]
      exact if_congr ⟨fun h => h ▸ hl, fun h => Fin.ext (by omega)⟩ rfl rfl
    rwa [e1, e2] at h
  rw [maps_iff_basis Q Q' α.b α.b' α.b'b (fun x hx => (GlobalTheory.T.split_place_lattice_component_integral_frame_coords α LS Q.lat hα hLS x).1 hx) _ hy]
  refine forall_congr' fun r => ?_
  have e : GlobalTheory.FinPl.rd α β (z.map (incA D)) *ᵥ (α.b' *ᵥ Pi.single r 1) = β.b' *ᵥ fun q => φ (z q r) := by
    rw [GlobalTheory.FinPl.rd, mulVec_mulVec, Matrix.mul_assoc, α.bb', Matrix.mul_one, ← mulVec_mulVec, mulVec_single_one]
    rfl
  rw [e, hasVal_col_iff P φ ψ hψ hres' (GlobalTheory.PhiOneVal.exists_denom_notMem_of_pr_int p P hP) Q' β.b β.b' β.bb'
    (fun x hx => (GlobalTheory.T.split_place_lattice_component_integral_frame_coords β LT Q'.lat hβ hLT x).1 hx) t hT]
  have e3 : ∀ q, toHom S T rfl rfl z (Pi.single r 1) q = z q r := by
    intro q
    simp [toHom]
  simp only [e3, mul_ite, mul_one, mul_zero]

end GlobalTheory.PhiOneVal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLevelPrimePhiOneEqOneIffColumnsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

theorem _root_.GlobalTheory.T.maps_rd_iff_colCond_toHom : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P →
    ∀ {S T : HSp D} {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (α : Frame p S (Fin S.rank)) (β : Frame p T (Fin T.rank))
    (Q : Pair k (Fin S.rank)) (Q' : Pair k (Fin T.rank)) (LS : Lat S) (LT : Lat T) (t : 𝓞 D.host.E),
    (∀ z, z ∈ LS ↔ z ∈ intVec D _) → (∀ z, z ∈ LT ↔ z ∈ intVec D _) → α.IsLat LS Q.lat → β.IsLat LT Q'.lat →
    (∀ w ∈ LS, ∀ r : Fin S.rank, r.1 + 1 = S.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q.HasVal (α.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    (∀ w ∈ LT, ∀ r : Fin T.rank, r.1 + 1 = T.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q'.HasVal (β.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (Maps Q Q' (GlobalTheory.FinPl.rd α β (z.map (incA D))) ↔ ColCond P t (toHom S T hS hT z)) := by
  first | exact @GlobalTheory.PhiOneVal.maps_rd_iff_colCond | exact GlobalTheory.PhiOneVal.maps_rd_iff_colCond | (intros; apply GlobalTheory.PhiOneVal.maps_rd_iff_colCond <;> assumption)
end
end
