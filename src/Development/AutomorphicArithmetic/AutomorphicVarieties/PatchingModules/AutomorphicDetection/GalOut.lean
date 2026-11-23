module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.S6
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlCSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.CotangentIndependentOfResidues
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.UrepStable
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlgebraMapMemSecondOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelScale
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OoExKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerRankBoundLaurent
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DiscImp

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.discImp :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ Q : Ideal S.Bh, Q.IsPrime → DiscSt (S.u.D.map (algebraMap S.B S.Bh)) Q → S.x.a = S.n ∨ ¬ ired S.U.N ≤ Q := by
  intro l _ S Q hQ hs
  rcases (UpperTheory.V.Pa.urep_stable S.U Q hQ).1 hs with ha | ⟨y, hy, z, hz, b, hb, e⟩
  · exact Or.inl ha
  · exact Or.inr fun hle => hb (hle (Ideal.subset_span ⟨y, hy, z, hz, e⟩))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EvenCocyclesLiftLaurent

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.k2F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), K2 h k → EvenCocyclesLiftLaurent h k := by
  intro l _ L G G0 h n x k hK z hz
  set f := algebraMap x.A x.Fr with hf
  have ht : f x.t ≠ 0 := by
    intro h0
    apply PowerSeries.X_ne_zero (R := x.K)
    exact IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)
  choose s₀ hs using fun i j => selScale l L G G0 h n x true (z i j) (hz i j).1 (hz i j).2
  set S := Finset.univ.sup (fun p : Fin (k.g + 1) × Fin k.g => s₀ p.1 p.2) with hSdef
  have hS : ∀ i j, s₀ i j ≤ S := fun i j =>
    Finset.le_sup (f := fun p : Fin (k.g + 1) × Fin k.g => s₀ p.1 p.2) (Finset.mem_univ (i, j))
  choose z' hz' hzz using fun i j => hs i j S (hS i j)
  obtain ⟨c, hc, Ψ, hΨ, hΨe⟩ := hK z' (fun i j => hz' i j)
  obtain ⟨hΨ1, hΨ2⟩ := selMap2 l L G G0 h n x k Ψ hΨ
  refine ⟨fun i => f (c i) * f x.t ^ S, ?_, _, hΨ1, hΨ2, ?_⟩
  · intro h0
    apply hc
    funext i
    have e := congrFun h0 i
    rcases mul_eq_zero.1 e with e | e
    · exact IsFractionRing.injective x.A x.Fr (e.trans (map_zero f).symm)
    · exact absurd e (pow_ne_zero S ht)
  · intro j γ a b
    have hz2 : ∀ i, f (z' i j γ a b) = f x.t ^ S * z i j γ a b := fun i => by
      have e := congrArg (fun M => M a b) (hzz i j γ)
      simpa using e
    show f ((Ψ γ a b).ep' j) = _
    rw [hΨe j γ a b]

    simp only [Matrix.sum_apply, Finset.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul, hz2]
    refine Finset.sum_congr rfl fun i _ => by ring
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PresOut0

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.presOut0 :
    ∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing B] [Algebra O B] [IsCO O B] (D0 : ℕ) (X : Fin D0 → B), (∀ a, X a ∈ maximalIdeal B) → maximalIdeal B ≤ Ideal.span (Set.range X) ⊔ ((maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2) → ∀ Z Q : Ideal B, Z.IsPrime → Q.IsPrime → ((1 + D0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Z) → Z ≤ Q := by
  intro O B _ _ _ _ _ _ _ D0 X hX hspan Z Q hZ hQ hdim
  haveI hOO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun a h => by simpa using h⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hA : IsCO O (MvPowerSeries (Fin D0) O) := co_mvps O O (Fin D0)
  obtain ⟨F, ⟨hFC, hFX⟩, -⟩ := co_ev O O B (Fin D0) (Algebra.ofId O B) X hX
  have hsurj : Function.Surjective F := by
    apply co_surj
    refine le_trans hspan (sup_le ?_ (sup_le ?_ le_sup_right))
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Ideal.mem_sup_left ?_
      rw [← hFX i]
      refine Ideal.mem_map_of_mem _ ?_
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
      simp
    · refine le_sup_of_le_left ?_
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have h1 : algebraMap O B a = F (MvPowerSeries.C a) := by
        rw [hFC]; rfl
      rw [h1]
      refine Ideal.mem_map_of_mem _ ?_
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
      simpa using ha
  have hdimA : ringKrullDim (MvPowerSeries (Fin D0) O) = 1 + (D0 : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp
  have hinj : ∀ r, F r ∈ Z → r = 0 := by
    intro r hr
    by_contra hne
    have hnz : r ∈ nonZeroDivisors (MvPowerSeries (Fin D0) O) := mem_nonZeroDivisors_of_ne_zero hne
    have hle := ringKrullDim_succ_le_of_surjective ((Ideal.Quotient.mk Z).comp F.toRingHom)
      ((Ideal.Quotient.mk_surjective).comp hsurj) hnz (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hr)
    rw [hdimA] at hle
    generalize ringKrullDim (B ⧸ Z) = d at hle hdim
    have hb : d ≠ ⊥ := ne_bot_of_le_ne_bot (WithBot.coe_ne_bot) hdim
    obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hb
    have h2 : (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) := hdim
    rw [WithBot.coe_le_coe] at h2
    have h1 : ((e + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((1 + D0 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      push_cast at hle ⊢; exact hle
    rw [WithBot.coe_le_coe] at h1
    have het : e ≠ ⊤ := by
      intro h; rw [h] at h1; simp at h1
    lift e to ℕ using het
    norm_cast at h1 h2
    omega
  have hZbot : Z = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨r, rfl⟩ := hsurj z
    rw [hinj r hz, map_zero]
    exact Ideal.zero_mem _
  rw [hZbot]
  exact bot_le
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.RfEx

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.rfEx :
    ∀ (K O B Bh : Type) [Field K] [CommRing O] [IsLocalRing O] [Algebra O K] [CommRing B] [Algebra O B] [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] (f : B →ₐ[O] PowerSeries K), IsCplAt B (RingHom.ker f) Bh → ∃ rF : Bh →+* FractionRing (PowerSeries K), (∀ b, rF (algebraMap B Bh b) = algebraMap (PowerSeries K) _ (f b)) ∧ RingHom.ker rF = maximalIdeal Bh := by
  intro K O B Bh _ _ _ _ _ _ _ _ _ f h
  haveI : IsAdicComplete (maximalIdeal (FractionRing (PowerSeries K))) (FractionRing (PowerSeries K)) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let φ : B →+* FractionRing (PowerSeries K) :=
    (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (f : B →+* PowerSeries K)
  have hcomap : Ideal.comap φ (maximalIdeal (FractionRing (PowerSeries K))) = RingHom.ker f := by
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    ext b
    simp only [RingHom.mem_ker, φ, RingHom.comp_apply, RingHom.coe_coe]
    exact map_eq_zero_iff _ (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift B (RingHom.ker f) Bh h (FractionRing (PowerSeries K)) φ hcomap
  refine ⟨ψ, fun b => RingHom.congr_fun hψ b, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hm
    have hu : IsUnit x := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hm
      exact hm
    exact (hu.map ψ).ne_zero (RingHom.mem_ker.mp hx)
  · have hm := IsCplAt.map_pow_eq B (RingHom.ker f) Bh h 1
    rw [pow_one, pow_one] at hm
    rw [← hm]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hψ]
    simp only [φ, RingHom.comp_apply, RingHom.coe_coe]
    rw [RingHom.mem_ker.mp ha, map_zero]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurentAlt

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.k3F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), K3 h k → SelmerSpannedByKappaLaurent h k := by
  intro l _ L G G0 h n x k hK z hz hb
  obtain ⟨s₀, hs⟩ := selScale l L G G0 h n x false z hz hb
  obtain ⟨z', hz', hzz⟩ := hs s₀ le_rfl
  obtain ⟨s', c, Y, hY, hYt, hYe⟩ := hK z' hz'
  set f := algebraMap x.A x.Fr with hf
  have ht : f x.t ≠ 0 := by
    intro h0
    apply PowerSeries.X_ne_zero (R := x.K)
    exact IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)
  have hsm : ∀ (a : x.A) (M : Matrix (Fin n) (Fin n) x.A), f.mapMatrix (a • M) = f a • M.map f := by
    intro a M
    ext i j
    simp
  have key : ∀ g, x.t ^ s' • z' g - ∑ j, c j • k.κ j (h.p₀ g) =
      x.ρX x.A (h.p₀ g) * Y * x.ρX x.A (h.p₀ g⁻¹) - Y := by
    intro g
    have e := congrFun hYe g
    simpa [dY, Finset.sum_apply] using e
  have key2 : ∀ g, f x.t ^ s' • (z' g).map f - ∑ j, f (c j) • kapF h k j g =
      x.ρX x.Fr (h.p₀ g) * Y.map f * x.ρX x.Fr (h.p₀ g⁻¹) - Y.map f := by
    intro g
    have e := congrArg f.mapMatrix (key g)

    simpa [map_sub, map_mul, map_sum, hsm, kapF, NP.ρX, Matrix.map_map, RingHom.mapMatrix_apply] using e
  set u := (f x.t ^ (s' + s₀))⁻¹ with hu
  refine ⟨fun j => u * f (c j), u • Y.map f, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨h1, h2⟩ := hY i j
    refine ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩
    have h3 := h1 hij
    rw [Submodule.mem_bot] at h3 ⊢
    simp [h3]
  · ext i j
    have h3 := congrFun (congrFun hYt i) j
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h3
    simp [Matrix.transpose_apply, h3]
  · funext g
    have e := key2 g
    rw [hzz g, smul_smul, ← pow_add] at e
    simp only [dY, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← e, smul_sub, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ ht), one_smul, Finset.smul_sum]
    simp [smul_smul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.GalOut

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

private theorem ctx_out {l : ℕ} [Fact l.Prime] (S : Ctx l) (D0 : ℕ) (h1 : K1 S.h S.k D0) (h2 : K2 S.h S.k) (h3 : K3 S.h S.k)
    (Z Q : Ideal S.Bh) (hZ : Z.IsPrime) (hQ : Q.IsPrime) (hs : DiscSt (S.u.D.map (algebraMap S.B S.Bh)) Z)
    (hd : ((1 + D0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (S.Bh ⧸ Z))
    (hq : DiscSt (S.u.D.map (algebraMap S.B S.Bh)) Q ∨ NonSS S.P.ker (algebraMap S.B S.Bh) Q) : Z ≤ Q := by
  obtain ⟨X, m, c, hX, hm, hc, hg, hr⟩ := pres l S D0 (k1F l _ _ _ S.h _ _ S.k D0 h1) (k2F l _ _ _ S.h _ _ S.k h2)
    (k3F l _ _ _ S.h _ _ S.k h3)
  by_cases ha : S.x.a = S.n
  · have hN := S.U.typeI ha
    have hi : ired S.U.N = ⊥ := by
      refine le_bot_iff.1 (Ideal.span_le.2 ?_)
      rintro b ⟨y, hy, z, -, e⟩
      rw [hN, Submodule.mem_bot] at hy
      rw [hy, zero_mul] at e
      exact S.U.inj (by rw [← e, map_zero])
    refine presOut0 S.OO S.Bh D0 X hX ?_ Z Q hZ hQ hd
    simpa only [Ctx.J2, hi, sup_bot_eq] using hg
  · haveI := S.U.fin
    refine presOut1 S.OO S.Bh S.U.AA S.U.N S.U.inj S.U.compl S.U.mul_mem D0 S.k.g X m c hX hm hc hg hr Z Q hZ hQ hd
      ((discImp l S Z hZ hs).resolve_left ha) ?_
    rcases hq with hq | hq
    · exact Or.inl ((discImp l S Q hQ hq).resolve_left ha)
    · exact Or.inr (S.U.thick Q hQ hq)

theorem galOut : GalOut := by
  intro l _ L G G0 h n x k O _ _ _ hO _ _ r B _ _ _ u P Bh _ _ _ D0 hl hc h1 h2 h3 Z Q hZ hQ hs hd hq
  haveI := hO.complete
  obtain ⟨rF, hf, hk⟩ := rfEx x.K O B Bh P.f hc
  obtain ⟨U⟩ := s6 l L G G0 h n x O r B u P Bh rF hl hc hf hk
  obtain ⟨OO, i1, i2, i3, i4, i5, i6, a1, a2, a3, a4⟩ := ooEx x.K O B Bh P.f P.s rF P.surj P.f_s hc hf
  exact ctx_out
    { odd := hl, L := L, G := G, G0 := G0, h := h, n := n, x := x, k := k, O := O, r := r, B := B, u := u, P := P, Bh := Bh,
      cpl := hc, rF := rF, rF_f := hf, rF_ker := hk, U := U, OO := OO, d6 := i6, oo_A := a1, oo_O := a2, ordinaryPointSection := a3, oo_surj := a4 }
    D0 h1 h2 h3 Z Q hZ hQ hs hd hq

end UpperTheory.V.Pa
end
end
