module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionsIndependentOnClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemNormWeightSumLeExpOfTest

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProjZeroPullbackNeZero

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

namespace GlobalTheory.ThetaInvPart

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem diag_eq [IsDomain o] {Q : Type} [AddCommGroup Q] [Fintype Q] (π : S.Gam →+ Q) (i₀ : S.J)
    (hc : Fintype.card S.J = Fintype.card Q)
    (hfix : ∀ a, π a = 0 → ∀ l, S.ρ a l i₀ = if l = i₀ then 1 else 0)
    (horb : ∀ i, ∃ a, ∃ e : ℕ, ∀ l, S.ρ a l i₀ = if l = i then S.ζ ^ e else 0) (a : S.Gam) :
    S.ρ a i₀ i₀ = if π a = 0 then 1 else 0 := by
  have hζ : S.ζ ≠ 0 := S.prim.ne_zero (pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega)
    (by have := S.N_ge; omega)))
  choose c e hce using horb
  have key : ∀ a b, π a = π b → ∃ k : ℕ, ∀ l, S.ρ b l i₀ = S.ζ ^ k * S.ρ a l i₀ := fun a b h => by
    obtain ⟨k, hk⟩ := S.ρ_mul b (a - b)
    refine ⟨k, fun l => ?_⟩
    have := congrFun (congrFun hk l) i₀
    rw [Matrix.mul_apply, add_sub_cancel, Matrix.smul_apply, smul_eq_mul] at this
    simpa [hfix (a - b) (by rw [map_sub, h, sub_self])] using this
  have inj : Function.Injective fun i => π (c i) := fun i j h => by
    obtain ⟨k, hk⟩ := key _ _ h
    by_contra hij
    have := hk j
    rw [hce, hce, if_pos rfl, if_neg (Ne.symm hij), mul_zero] at this
    exact pow_ne_zero _ hζ this
  have surj := ((Fintype.bijective_iff_injective_and_card _).2 ⟨inj, hc⟩).2
  have zero : ∀ a i, π (c i) = π a → i ≠ i₀ → S.ρ a i₀ i₀ = 0 := fun a i h hi => by
    obtain ⟨k, hk⟩ := key _ _ h
    rw [hk, hce, if_neg (Ne.symm hi), mul_zero]
  split_ifs with ha
  · rw [hfix a ha, if_pos rfl]
  · obtain ⟨i, hi⟩ := surj (π a)
    refine zero a i hi fun h => ?_
    obtain ⟨j, hj⟩ := surj (π 0)
    by_cases h' : j = i₀
    · exact ha (by rw [← hi, h, ← h', hj, map_zero])
    · have := zero 0 j hj h'
      rw [hfix 0 (map_zero π), if_pos rfl] at this
      exact one_ne_zero this

theorem rho_fix (hG : GlobalFnsSt) (hi : Function.Injective (algebraMap o Ω)) (ρ : S.Real) (a : S.Gam)
    (ha : (ρ.n ^ ρ.k) • S.r • a = 0) (l : S.J) : S.ρ a l ρ.i₀ = if l = ρ.i₀ then 1 else 0 := by
  have := ρ.P.isAb.comm
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hm : ρ.pt (S.r • a) ^ (ρ.n ^ ρ.k) = 1 := by rw [← hp, ha, h0]
  have hN : ρ.pt (S.r • a) ^ S.N = 1 :=
    (congrArg _ (ρ.N_eq.trans (sq _))).trans (by rw [pow_mul, hm, one_pow])
  obtain ⟨ν, hν⟩ := exists_gen_negLB hG _ ρ.P 1 (baseOver (Sp S.R))
  have hact := ThetaCoord.isActOf_self hG ρ.P.isAb ρ.P.isLB (q := S.N) (b := 1)
    (by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow) hν ρ.α_gen ρ.s_zero hm hN (ρ.U_sym a)
  have h₁ := ρ.U_act a ρ.i₀ _ hact
  have h₂ : ∀ j, (ρ.s ρ.i₀).f j = ∑ l, liftFun ρ.P.A _ (fn (algebraMap o S.R (if l = ρ.i₀ then 1 else 0))) *
      (ρ.s l).f j := fun j => by
    rw [Finset.sum_eq_single ρ.i₀ (fun b _ hb => by simp [hb, liftFun]) (by simp)]
    simp [liftFun]
  have h₃ := congrFun ((ρ.s_basis (ρ.s ρ.i₀)).unique h₁ h₂) l
  have h₄ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv).1 h₃
  exact hi (congrArg Subtype.val h₄)

end GlobalTheory.ThetaInvPart

namespace GlobalTheory

open ThetaInvPart

theorem proj_zero_pullback_ne_zero : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (S : ThetaSys o Ω) (ρ : S.Real) (k : Type) [Field k] (y : o →+* k) (T : AddSubgroup S.Gam), S.IsoFree T →
    ∃ j, y (S.proj T 0 j ρ.i₀) ≠ 0 := by
  intro hL o Ω _ _ _ hA S ρ k _ y T _
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero (ρ.n ^ ρ.k) := ⟨pow_ne_zero _ ρ.n_prime.ne_zero⟩
  have : IsDomain o := hA.inj.isDomain _
  have hd : ρ.n ^ ρ.k ∣ S.r * S.N := by
    rw [ρ.N_eq]; exact Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) _
  let π : S.Gam →+ (Fin S.g ⊕ Fin S.g → ZMod (ρ.n ^ ρ.k)) :=
    (ZMod.castHom hd (ZMod (ρ.n ^ ρ.k))).toAddMonoidHom.compLeft _
  have hdiag := diag_eq π ρ.i₀ (by
      rw [ρ.card, ρ.N_eq, ← pow_mul]
      simp [two_mul])
    (fun a ha => rho_fix hL.1.globalFns hA.inj ρ a (funext fun i => by
      have h : ZMod.castHom hd (ZMod (ρ.n ^ ρ.k)) (a i) = 0 := congrFun ha i
      rw [← ZMod.natCast_zmod_val (a i), map_natCast, ZMod.natCast_eq_zero_iff] at h
      obtain ⟨c, hc⟩ := h
      rw [Pi.smul_apply, Pi.smul_apply, ← ZMod.natCast_zmod_val (a i), hc, nsmul_eq_mul, nsmul_eq_mul,
        ← Nat.cast_mul, ← Nat.cast_mul, Pi.zero_apply, ZMod.natCast_eq_zero_iff]
      exact ⟨c, by rw [ρ.N_eq]; ring⟩)) ρ.orbit
  have hu : ∀ n : ℕ, n ∣ Nat.card S.Gam → IsUnit (n : o) := fun n hn => by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast hn) ?_
    rw [Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  refine ⟨ρ.i₀, (IsUnit.map y ?_).ne_zero⟩
  have := Fintype.ofFinite T
  have hT := AddSubgroup.card_addSubgroup_dvd_card T
  have hK := (AddSubgroup.card_addSubgroup_dvd_card (π.comp T.subtype).ker).trans hT
  have hs : ∑ t : T, S.ρ t ρ.i₀ ρ.i₀ = (Nat.card (π.comp T.subtype).ker : o) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hdiag]
    by_cases h : π t = 0 <;> simp [AddMonoidHom.mem_ker, h]
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp only [AddMonoidHom.zero_apply, neg_zero, ZMod.val_zero, pow_zero, one_smul]
  rw [hs]
  exact (hu _ hT).ringInverse.mul (hu _ hK)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPullbackNonzeroOnClosedFibre

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ThetaFibre

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem proj_mulVec_mem (hB : BaseFacts S M U₀ EE) (z : M.Z) {v : S.J → Ω} (hv : v ∈ EE.E z) :
    ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v ∈ EE.E z := by
  have hT : S.TT M z ≤ S.HH M z := (hB.free z).2 ▸ (hB.free z).1.1
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have := Fintype.ofFinite (S.TT M z)
  have e : ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v =
      algebraMap o (M.O z) (Ring.inverse (Nat.card (S.TT M z) : o)) •
        ∑ t : S.TT M z, ((S.ρ t).map (algebraMap o Ω)).mulVec v := by
    ext i
    simp [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.mulVec, dotProduct, Matrix.sum_apply,
      Algebra.smul_def (A := Ω), Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => hB.stab z _ (hT t.2) v hv)

theorem proj_mulVec_regular (hB : BaseFacts S M U₀ EE) {z : M.Z} (hz : IsClosed ({z} : Set M.Z))
    {v : S.J → Ω} (hv : v ∈ EE.E z) (j : S.J) :
    ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v j ∈ M.O z := by
  refine hB.zero z hz _ (proj_mulVec_mem hB z hv) ?_ j
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
    GlobalTheory.ThetaBound.proj_mul_proj S _ _ le_rfl (hB.free z).1.1 (hB.free z).1 0 0 fun _ => rfl]

theorem proj_col_eq_zero (hB : BaseFacts S M U₀ EE) {z : M.Z} (hz : IsClosed ({z} : Set M.Z))
    {K : Type} [Field K] (y : M.O z →+* K) (B : Matrix S.J S.J Ω) (hBm : ∀ k, B k ∈ EE.E z)
    (a : S.J → M.O z) (i : S.J) (ha : ∀ j, ∑ k, (a k : Ω) * B k j = (1 : Matrix S.J S.J Ω) i j)
    (h0 : ∀ k, y (a k) = 0) (j : S.J) :
    y (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i)) = 0 := by
  have e : algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i) =
      ∑ k, a k * ⟨_, proj_mulVec_regular hB hz (hBm k) j⟩ := by
    apply Subtype.ext
    have h1 : ∑ m, algebraMap o Ω (S.proj (S.TT M z) 0 j m) * (1 : Matrix S.J S.J Ω) i m =
        algebraMap o Ω (S.proj (S.TT M z) 0 j i) := by
      simp [Matrix.one_apply]
    simp only [Subalgebra.coe_algebraMap, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
    rw [← h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ha, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

  rw [e, map_sum]
  exact Finset.sum_eq_zero fun k _ => by rw [map_mul, h0, zero_mul]

theorem exists_mem_nonzeroLocus_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ x ∈ nonzeroLocus (Q.st ρ.i₀), x ∈ Q.G ∧ Q.P.hom x = z := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q hbig hgeo z hz
  by_contra hne
  have hzc : z ∈ ⨆ l, Q.W l := by rw [Q.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hzc
  obtain ⟨K, _, x, hx, hind⟩ := GlobalTheory.T.thetaSections_independent_on_closed_fibre hL o Ω S ρ M U₀ EE hB Q hbig hgeo l z hl hz
  have hc : (fun k => valF x (Q.W l) (Q.c l ρ.i₀ k)) = 0 := by
    refine hind _ fun g j hg hgx => ?_
    by_cases hj : ⊤ ≤ g ⁻¹ᵁ (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι).U j
    · have hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) g
          (fun i => valF g _ ((Q.σ l i).f j)) :=
        ⟨j, 1, hj, fun i => by rw [Units.val_one, _root_.one_mul]; rfl⟩
      have hr := Q.rel l K g _ hw
      rw [hgx] at hr
      by_contra h0
      have hu := (CrdCalc.crd_isUnit_iff ρ.i₀ hr).1 (isUnit_iff_ne_zero.2 h0)
      refine hne ⟨(g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (IsLocalRing.closedPoint K), hu (Set.mem_univ _),
        hg ⟨_, rfl⟩, ?_⟩
      have hm : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rw [hx] at hm
      rw [← hgx] at hm
      exact hm
    · exact Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (dif_neg hj)
  obtain ⟨j, hj⟩ := GlobalTheory.proj_zero_pullback_ne_zero hL o Ω S ρ K
    ((RatModel.valHom x z hx).comp (algebraMap o (M.O z))) _ (hB.free z).1
  refine hj (proj_col_eq_zero hB hz (RatModel.valHom x z hx) (Q.B l)
    (fun k => by rw [Q.basis l z hl]; exact Submodule.subset_span ⟨k, rfl⟩)
    (fun k => ⟨_, RatModel.valF_mem_O hl (Q.c l ρ.i₀ k)⟩) ρ.i₀
    (fun j => congrFun (congrFun (Q.c_inv l) ρ.i₀) j) (fun k => ?_) j)
  rw [RatModel.valHom_apply, RatModel.val_valF (by rw [hx]; exact Set.singleton_subset_iff.2 hl)]
  exact congrFun hc k

end GlobalTheory.ZH.ThetaFibre
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPullbackNonzeroOnClosedFibreStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_theta_pullback_nonzero_on_closed_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ x ∈ nonzeroLocus (Q.st ρ.i₀), x ∈ Q.G ∧ Q.P.hom x = z := by
  first | exact @GlobalTheory.ZH.ThetaFibre.exists_mem_nonzeroLocus_fibre | exact GlobalTheory.ZH.ThetaFibre.exists_mem_nonzeroLocus_fibre | (intros; apply GlobalTheory.ZH.ThetaFibre.exists_mem_nonzeroLocus_fibre <;> assumption)
end
end
