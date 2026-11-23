module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.LiftPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.BaseBc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.MapsBc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.RingBc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilLam
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ChainLift
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.DiscStMap
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.IsProLOfPL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.MemSpanMapE0kerOfPairMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.NonSSField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.NonSSMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Oprime
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairMf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PtLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ResidBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilCo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.KerMapPowerSeriesQuotient
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AutBc

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.aut_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (T : TWGrp G0) (_A : TWAut u J Empty D T), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → ∃ A' : TWAut u' (J.map (Til.ι O O' B)) Unit D T, A'.b.lam (MvPowerSeries.X (.inl ())) = Til.s O O' B := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D T A hr hu
  obtain ⟨τ, hτ, hs⟩ := UpperTheory.V.Pa.BC.til_lam O O' D
  obtain ⟨τS, hS⟩ := UpperTheory.V.Pa.BC.sinf_iso l O O' D T.q n τ hτ
  obtain ⟨b', hb⟩ := UpperTheory.V.Pa.BC.base_bc l L G0 n O O' r r' B u u' J D A.b τ hr hu hτ
  have hA := fun N => UpperTheory.V.Pa.BC.ring_bc l L G0 n O O' r r' B u u' J D A.b b' τ (T.GN N) (T.h N) T.q A.ut N τS
    (A.A N) hr hu hb hS
  choose A' hA' using hA
  have hm := fun N => UpperTheory.V.Pa.BC.maps_bc l L G0 n O O' r r' B u u' J D A.b b' τ (T.GN N) (T.h N) T.q A.ut N τS
    (A.A N) (A' N) (T.Nq N) (T.ph N) (T.ta N) A.ex (A.m N) hr hu hb hS (hA' N)
  refine ⟨⟨b', fun j i => algebraMap O O' (A.ut j i), ?_, A', A.ex, fun N => (hm N).some⟩, ?_⟩
  · intro j i
    rw [hr.1 i, ← ResidueField.map_residue, A.ut_res]
    rfl
  · obtain ⟨hb⟩ := hb
    show b'.lam _ = _
    rw [← hs, hb.lam, Til.map_s]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ChainTens

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.chain_tens :
    ∀ (O O' B : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [IsLocalRing O] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] [CommRing B] [Algebra O B] (h : ℕ) (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) → (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) → (∃ (P : Fin (h + 1) → Ideal (O' ⊗[O] B)) (E : Fin h → Ideal (O' ⊗[O] B)), (∀ i, (P i).IsPrime ∧ (P i).comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = p i) ∧ ∀ i, (E i).IsPrime ∧ (E i).comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = e i ∧ E i ≤ P i.castSucc ∧ E i ≤ P i.succ) ∧ ∀ (P : Ideal (O' ⊗[O] B)) (q : Ideal B), P.IsPrime → q.IsPrime → q ≤ P.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) → ∃ Q : Ideal (O' ⊗[O] B), Q.IsPrime ∧ Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = q ∧ Q ≤ P := by
  intro O O' B _ _ _ _ _ _ _ _ _ h p e hp he
  letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  let φ : B ⊗[O] O' ≃ₐ[B] O' ⊗[O] B := Algebra.TensorProduct.commRight O B O'
  haveI : Module.Finite B (O' ⊗[O] B) := Module.Finite.equiv φ.toLinearEquiv
  haveI : Module.Free B (O' ⊗[O] B) := Module.Free.of_equiv φ.toLinearEquiv
  haveI : Module.FaithfullyFlat O O' := inferInstance
  haveI : Module.FaithfullyFlat B (O' ⊗[O] B) :=
    Module.FaithfullyFlat.of_linearEquiv B (B ⊗[O] O') φ.symm.toLinearEquiv
  haveI : FaithfulSMul B (O' ⊗[O] B) := inferInstance
  exact UpperTheory.V.Pa.BC.chain_lift B (O' ⊗[O] B) h p e hp he
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.GenBc

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.gen_bc :
    ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (S : Set B) (S' : Set (Til O O' B)), IsLocalHom (Til.ι O O' B) → Til.s O O' B ∈ maximalIdeal (Til O O' B) → (∀ a ∈ S, Til.ι O O' B a ∈ S') → Til.s O O' B ∈ S' → GenBy O S → GenBy O' S' := by
  intro O O' _ _ _ _ _ _ _ B _ _ _ _ S S' hloc hs hS hsS hgen N
  let P : Til O O' B → Prop := fun x => ∃ a ∈ Algebra.adjoin O' S', x - a ∈ maximalIdeal (Til O O' B) ^ N
  have Pmem : ∀ x ∈ Algebra.adjoin O' S', P x := fun x hx => ⟨x, hx, by simp⟩
  have Padd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a + b, add_mem ha hb, ?_⟩
    have : x + y - (a + b) = (x - a) + (y - b) := by ring
    rw [this]
    exact add_mem hx hy
  have Pmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_mem ha hb, ?_⟩
    have : x * y - a * b = x * (y - b) + (x - a) * b := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hx)
  have hadj : ∀ a ∈ Algebra.adjoin O S, Til.ι O O' B a ∈ Algebra.adjoin O' S' := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (hS x hx)
    | algebraMap r => rw [Til.ι_algebraMap]; exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hmap : Ideal.map (Til.ι O O' B) (maximalIdeal B ^ N) ≤ maximalIdeal (Til O O' B) ^ N := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit (Til.ι O O' B) x hx
  have Pι : ∀ b, P (Til.ι O O' B b) := by
    intro b
    obtain ⟨a, ha, hb⟩ := hgen N b
    refine ⟨_, hadj a ha, ?_⟩
    rw [← map_sub]
    exact hmap (Ideal.mem_map_of_mem _ hb)
  have PC : ∀ t, P (Til.C O O' B t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add (f := _)]; exact Padd _ _ hx hy
    | tmul o b =>
      have h : algebraMap O' (Til O O' B) o = Til.C O O' B (algebraMap O' (O' ⊗[O] B) o) :=
        PowerSeries.algebraMap_apply
      have e : Til.C O O' B (o ⊗ₜ[O] b) = algebraMap O' (Til O O' B) o * Til.ι O O' B b := by
        rw [h]
        show _ = Til.C O O' B _ * Til.C O O' B ((1 : O') ⊗ₜ[O] b)
        rw [← map_mul]
        congr 1
        simp
      rw [e]
      exact Pmul _ _ (Pmem _ (Subalgebra.algebraMap_mem _ _)) (Pι b)
  have hsA : Til.s O O' B ∈ Algebra.adjoin O' S' := Algebra.subset_adjoin hsS
  have hdec : ∀ f : Til O O' B, ∃ (g : Til O O' B) (c : O' ⊗[O] B), f = Til.s O O' B * g + Til.C O O' B c :=
    fun f => ⟨_, _, PowerSeries.eq_X_mul_shift_add_const (R := O' ⊗[O] B) f⟩
  have key : ∀ (k : ℕ) (f : Til O O' B), ∃ g h, P g ∧ f = g + Til.s O O' B ^ k * h := by
    intro k f
    induction k with
    | zero => exact ⟨0, f, Pmem _ (zero_mem _), by simp⟩
    | succ k ih =>
      obtain ⟨g, h, hg, e⟩ := ih
      obtain ⟨h', c, e'⟩ := hdec h
      refine ⟨g + Til.s O O' B ^ k * Til.C O O' B c, h',
        Padd _ _ hg (Pmul _ _ (Pmem _ (pow_mem hsA k)) (PC c)), ?_⟩
      rw [e, e']
      ring
  intro f
  obtain ⟨g, h, hg, e⟩ := key N f
  rw [e]
  refine Padd _ _ hg ⟨0, zero_mem _, ?_⟩
  rw [sub_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hs N)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilPrime

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_prime :
    ∀ (O O' B : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [CommRing B] [Algebra O B] [IsNoetherianRing B] (Q : Ideal (O' ⊗[O] B)), Q.IsPrime → (Q.map (Til.C O O' B)).IsPrime ∧ (Q.map (Til.C O O' B)).comap (Til.ι O O' B) = Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) := by
  intro O O' B _ _ _ _ _ _ _ Q hQ
  haveI hN : IsNoetherianRing (O' ⊗[O] B) := by
    letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
    haveI : Module.Finite B (O' ⊗[O] B) :=
      Module.Finite.equiv (Algebra.TensorProduct.commRight O B O').toLinearEquiv
    exact Algebra.FiniteType.isNoetherianRing B (O' ⊗[O] B)
  obtain ⟨-, -, h3, h4⟩ := UpperTheory.V.AlgebraTools.powerSeries_ker_map (O' ⊗[O] B) Q (IsNoetherian.noetherian Q)
  refine ⟨h3 hQ, ?_⟩
  have h5 : (Q.map (Til.C O O' B)).comap (Til.C O O' B) = Q := h4
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap]
  conv_rhs => rw [← h5]
  exact Iff.rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.CoreBC

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W
open scoped TensorProduct

namespace UpperTheory.V.Pa

theorem coreBC : CoreBC := by
  intro l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D A0 hl hP hAd hG h x hx
  obtain ⟨O', _, _, _, _, α, P, hco, hfin, hfree, hloc, hcard, hα, hPm, hPα, hsplit⟩ :=
    BC.oprime l O (x 0).x.K
  letI : Algebra ℤ_[l] O' := ((algebraMap O O').comp (algebraMap ℤ_[l] O)).toAlgebra
  haveI : IsScalarTower ℤ_[l] O O' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)
  haveI : Finite (ResidueField O) := IsCoef.finite (l := l)
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨⟨r', hr'⟩, hrr⟩ := BC.resid_bc l G0.frame O O' n r
  obtain ⟨hrIp, -, hrchi⟩ := hrr r' hr'
  obtain ⟨hTco, hιloc, hsm⟩ := BC.til_co O O' B
  obtain ⟨-, u', hu'⟩ := BC.pair_bc l G0.frame O O' n r r' hr' B (Til O O' B) (Til.ι O O' B)
    (Til.ι_algebraMap O O' B) u
  obtain ⟨A', hA'⟩ := BC.aut_bc l L G0 n O O' r r' B u u' J D T A0 hr' hu'
  have hphi := BC.phi0 l L G0 T hP
  have hAd' : Adapted (r := r') T :=
    ⟨fun g hg i => (hrchi i g).2 (hAd.1 g hg i), fun w => (hrIp w).trans (hAd.2 w)⟩
  have hG' : GenBy O' (pairVals u' ∪ {A'.b.lam (MvPowerSeries.X (Sum.inl ()))}) := by
    refine BC.gen_bc O O' B (pairVals u) _ hιloc hsm ?_ ?_ hG
    · rintro a (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩)
      · left; left
        refine ⟨i, g, ?_⟩
        have h3 := ((CA.d_gmap u.D).2.2.1 (Til.ι O O' B) (MonoidAlgebra.single g 1)).2 i
        rw [MonoidAlgebra.mapRingHom_single, map_one, hu'.1] at h3
        exact h3.symm
      · left; right
        exact ⟨v, i, g, by rw [← hu'.2 v i]; rfl⟩
    · right; rw [hA']; rfl
  have hpr : ∀ i, (RingHom.ker (x i).f).IsPrime := fun i => RingHom.ker_isPrime _
  intro e he hq1 q hq hqle hst
  obtain ⟨⟨Pt', Et, hPt, hEt⟩, hdown⟩ := BC.chain_tens O O' B h (fun i => RingHom.ker (x i).f) e hpr
    (fun i => ⟨(he i).1, (he i).2.2⟩)
  have hl1 := fun i => BC.pt_lift l O O' α P B (x i).x.K (x i).f (Pt' i) hα hPm hPα
    (hsplit _ (hx i)) (hcard.trans (hx i).symm) (hPt i).1 (hPt i).2
  choose inst f' hsurj hfι hfs hker using hl1
  have hmaps : ∀ i, u'.Maps (f' i).toRingHom (GDet.ofRep (mat (x i).x.ρ)) (x i).x.ψ := by
    intro i
    have hc : (f' i).toRingHom.comp (Til.ι O O' B) = (x i).f.toRingHom := RingHom.ext (hfι i)
    refine ⟨?_, fun v j => ?_⟩
    · rw [← hu'.1, (CA.d_gmap u.D).2.1, hc]
      exact (x i).maps.1
    · rw [← hu'.2 v j, ← (x i).maps.2 v j, ← hc]
      rfl
  let x' : Fin (h + 1) → Pt T u' (D + n * T.q) := fun i =>
    @Pt.mk _ _ _ _ T _ _ _ _ _ r' _ _ _ _ u' _ (x i).x (inst i) (x i).k (x i).al (x i).eig (x i).b1 (x i).b2
      (f' i) (hmaps i)
  have hmain := core l L G0 T n O' r' (Til O O' B) u' _ D A' hl hP hAd' hG' h x'
    (fun i => ⟨hsurj i, by rw [hA']; exact hfs i⟩)
  have hup : ∀ Q : Ideal (O' ⊗[O] B), Q.IsPrime →
      (Ideal.map (Til.C O O' B) Q).IsPrime ∧
        Ideal.comap (Til.ι O O' B) (Ideal.map (Til.C O O' B) Q) =
          Ideal.comap Algebra.TensorProduct.includeRight Q :=
    fun Q hQ => BC.til_prime O O' B Q hQ
  have hle : ∀ (Q : Ideal (O' ⊗[O] B)) i, Q ≤ Pt' i →
      Ideal.map (Til.C O O' B) Q ≤ RingHom.ker (x' i).f := by
    intro Q i hQi
    rw [Ideal.map_le_iff_le_comap]
    exact hQi.trans (hker i).ge
  have hfinI : ∃ s : Finset G0.frame.G₀, ∀ y : MonoidAlgebra B G0.frame.G₀, ∃ c : G0.frame.G₀ → B,
      y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ TwoSidedIdeal.span (augmentationIdealKernel u) := by
    obtain ⟨s, hs⟩ := (BC.pair_mf l G0.frame O n r B u hphi).2.2 (pairGens u)
    exact ⟨s, fun y => (hs y).imp fun c hc => TwoSidedIdeal.subset_span hc⟩
  have hns : ∀ (E : Ideal (Til O O' B)) (e0 : Ideal B), E.IsPrime →
      Ideal.comap (Til.ι O O' B) E = e0 → NonSS (augmentationIdealKernel u) (RingHom.id B) e0 →
        NonSS (augmentationIdealKernel u') (RingHom.id _) E := by
    intro E e0 hE hEe h0
    have h1 : NonSS (augmentationIdealKernel u) (Til.ι O O' B) E :=
      BC.nonSS_field B B (Til O O' B) G0.frame.G₀ (augmentationIdealKernel u) (RingHom.id B) (Til.ι O O' B) e0 E hE
        (by rw [hEe, Ideal.comap_id]) hfinI h0
    refine BC.nonSS_mono B (Til O O' B) (Til O O' B) G0.frame.G₀ G0.frame.G₀ (MonoidHom.id _)
      (augmentationIdealKernel u) (augmentationIdealKernel u') (Til.ι O O' B) (RingHom.id _) E (fun g => ⟨g, rfl⟩) ?_ h1
    intro z hz
    rw [MonoidAlgebra.mapRingHom_id, MonoidAlgebra.mapDomainRingHom_id]
    exact BC.mem_span_map_e0ker_of_pair_maps l G0.frame O O' n r r' B (Til O O' B) u u' (Til.ι O O' B) hphi hrIp
      (fun a => Til.ι_algebraMap O O' B _) hu' z hz
  have hds : ∀ (E : Ideal (Til O O' B)), DiscSt u.D (Ideal.comap (Til.ι O O' B) E) → DiscSt u'.D E := by
    intro E hE
    rw [← hu'.1]
    exact ((BC.discSt_map n B (Til O O' B) G0.frame.G₀ u.D).1 (Til.ι O O' B) E).2 hE
  obtain ⟨q₁, hq₁, hq₁d, hJq₁, hq₁le⟩ := hq1
  obtain ⟨Q₁, hQ₁, hQ₁c, hQ₁le⟩ := hdown (Pt' 0) q₁ (hPt 0).1 hq₁ (by rw [(hPt 0).2]; exact hq₁le)
  obtain ⟨Q, hQ, hQc, hQle⟩ := hdown (Pt' (Fin.last h)) q (hPt _).1 hq (by rw [(hPt _).2]; exact hqle)
  have hEp : ∀ i, (Ideal.map (Til.C O O' B) (Et i)).IsPrime ∧
      Ideal.comap (Til.ι O O' B) (Ideal.map (Til.C O O' B) (Et i)) = e i := fun i =>
    ⟨(hup _ (hEt i).1).1, (hup _ (hEt i).1).2.trans (hEt i).2.1⟩
  have hq' := (hup Q hQ).2.trans hQc
  have hfin := hmain (fun i => Ideal.map (Til.C O O' B) (Et i))
    (fun i => ⟨(hEp i).1, hns _ _ (hEp i).1 (hEp i).2 (he i).2.1, hle _ _ (hEt i).2.2.1,
      hle _ _ (hEt i).2.2.2⟩)
    ⟨Ideal.map (Til.C O O' B) Q₁, (hup _ hQ₁).1,
      hds _ (by rw [(hup _ hQ₁).2, hQ₁c]; exact hq₁d),
      by rw [Ideal.map_le_iff_le_comap, (hup _ hQ₁).2, hQ₁c]; exact hJq₁,
      hle _ _ hQ₁le⟩
    (Ideal.map (Til.C O O' B) Q) (hup _ hQ).1 (hle _ _ hQle)
    (by
      rcases hst with hd | hn
      · exact Or.inl (hds _ (by rw [hq']; exact hd))
      · exact Or.inr (hns _ _ (hup _ hQ).1 hq' hn))
  intro b hb
  rw [← hq']
  exact hfin (Ideal.mem_map_of_mem _ hb)

end UpperTheory.V.Pa
end
end
