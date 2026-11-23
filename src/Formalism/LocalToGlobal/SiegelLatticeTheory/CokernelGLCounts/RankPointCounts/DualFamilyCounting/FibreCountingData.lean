module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapes
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DivMulMemSPOfSub
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingDataMore
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsSubDivMemSP
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SpanPowMulLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CondZIff

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingDataFurther

section

@[expose] public section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

namespace JD

variable (J : JD h L 𝔭 b a)
include J

theorem crd_phi (z : Fin m → 𝓞 K) (k : Fin m) :
    crd h b a (G2.phi (K := K) b a z) k = jK (z k) / jK (ι (a k)) := by
  rw [crd, h_phi J.orth J.diag J.ne]

theorem phi_memA (z : Fin m → 𝓞 K) : G2.phi (K := K) b a z ∈ locF 𝔭 (dualIn h ⊤ L) := by
  have := J.max.isPrime
  rw [J.memA]
  intro i
  rw [← h_b J.orth J.diag J.ne, h_phi J.orth J.diag J.ne]
  exact HU.jK_mem_SP _

def Psi : (Fin m → 𝓞 K) →ₗ[𝓞 K] DiscMod h ⊤ L 𝔭 :=
  ((locF 𝔭 L).comap (locF 𝔭 (dualIn h ⊤ L)).subtype).mkQ ∘ₗ
    LinearMap.codRestrict _ (G2.phi (K := K) b a) J.phi_memA

theorem Psi_apply (z : Fin m → 𝓞 K) :
    J.Psi z = Submodule.Quotient.mk ⟨G2.phi (K := K) b a z, J.phi_memA z⟩ := rfl

theorem Psi_surjective : Function.Surjective J.Psi := by
  have := J.max.isPrime
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx := (J.memA x).1 x.2
  choose z hz using fun i => exists_sub_div_mem_SP J.max (J.ne i) (hx i)
  refine ⟨z, ?_⟩
  rw [Psi_apply, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.coe_sub, J.memB]
  intro k
  rw [crd_sub, J.crd_phi]
  have e : jK (z k) / jK (ι (a k)) - crd h b a x k =
      -((jK (ι (a k)) * crd h b a x k - jK (z k)) / jK (ι (a k))) := by
    rw [sub_div, mul_div_cancel_left₀ _ (jK_ι_ne_zero (K := K) (J.ne k))]
    exact (neg_sub _ _).symm
  rw [e]
  exact neg_mem (hz k)

theorem exists_E_eq (P : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭))
    (hP : ∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
      Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
      h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    ∃ (Y : Matrix (Fin m) (Fin m) (𝓞 K))
      (hY : ∀ i j, haveI := J.max.isPrime; jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭),
      (∀ i j, haveI := J.max.isPrime;
        jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) ∈ HU.SP K 𝔭) ∧ J.E Y hY = P := by
  have := J.max.isPrime
  set u : Fin m → ↥(locF 𝔭 (dualIn h ⊤ L)) :=
    fun j => ⟨G2.phi (K := K) b a (Pi.single j 1), J.u_mem j⟩ with hu
  choose v hv using fun j => Submodule.Quotient.mk_surjective _ (P (Submodule.Quotient.mk (u j)))

  have hav : ∀ j k, jK (ι (a j)) * crd h b a (v j) k ∈ HU.SP K 𝔭 := by
    intro j k
    have h0 : (ι (a j)) • (Submodule.Quotient.mk (u j) : DiscMod h ⊤ L 𝔭) = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.subtype_apply, Submodule.coe_smul, J.memB]
      intro l
      simp only [hu, crd_smul, J.crd_u]
      by_cases hl : l = j
      · rw [ite_eq_left hl, mul_one_div, div_self (jK_ι_ne_zero (K := K) (J.ne j))]
        exact one_mem _
      · rw [ite_eq_right hl, mul_zero]
        exact zero_mem _
    have h1 : (Submodule.Quotient.mk (ι (a j) • v j) : DiscMod h ⊤ L 𝔭) = 0 := by
      rw [Submodule.Quotient.mk_smul, hv j, ← LinearMap.map_smul, h0, map_zero]
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_smul, J.memB] at h1
    have h2 := h1 k
    rwa [crd_smul] at h2
  choose z hz using fun k j => exists_sub_div_mem_SP J.max (J.ne j) (hav j k)
  set Y : Matrix (Fin m) (Fin m) (𝓞 K) := Matrix.of z with hY
  have hcg : ∀ j k, crd h b a (gmap h b a Y (u j)) k = jK (Y k j) / jK (ι (a j)) := by
    intro j k
    rw [J.crdG]
    exact J.sum_crd_u _ j

  have hgv : ∀ j, gmap h b a Y (u j) - v j ∈ locF 𝔭 L := by
    intro j
    rw [J.memB]
    intro k
    rw [crd_sub, hcg]
    have e : jK (Y k j) / jK (ι (a j)) - crd h b a (v j) k =
        -((jK (ι (a j)) * crd h b a (v j) k - jK (z k j)) / jK (ι (a j))) := by
      rw [sub_div, mul_div_cancel_left₀ _ (jK_ι_ne_zero (K := K) (J.ne j)), hY, of_apply]
      exact (neg_sub _ _).symm
    rw [e]
    exact neg_mem (hz k j)
  have hgA : ∀ j, gmap h b a Y (u j) ∈ locF 𝔭 (dualIn h ⊤ L) := fun j => by
    have := add_mem (B_le_A J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat _ (hgv j)) (v j).2
    rwa [sub_add_cancel] at this
  have hYA : ∀ i j, jK (ι (a i) * Y i j) / jK (ι (a j)) ∈ HU.SP K 𝔭 := by
    intro i j
    have := (J.memA _).1 (hgA j) i
    rwa [hcg, ← mul_div_assoc, ← map_mul] at this
  refine ⟨Y, hYA, ?_, ?_⟩
  · intro i j
    have hsum : ∑ p, ∑ q, star (crd h b a (u i) p) * jK (gramO a Y p q) * crd h b a (u j) q =
        jK (gramO a Y i j) / (jK (ι (a i)) * jK (ι (a j))) := by
      refine (Finset.sum_congr rfl fun p _ =>
        J.sum_crd_u (fun q => star (crd h b a (u i) p) * jK (gramO a Y p q)) j).trans ?_
      rw [Finset.sum_eq_single i]
      · simp only [hu]
        rw [J.crd_u, ite_eq_left rfl, star_div₀, star_one, star_jK_ι J.fix, one_div_mul_eq_div, div_div]
      · intro p _ hp
        simp only [hu]
        rw [J.crd_u, ite_eq_right hp, star_zero, zero_mul, zero_div]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [← hsum, ← form_identity J.orth J.diag J.ne J.bX J.loc J.fix J.max J.lat]
    have e : h (gmap h b a Y (u i)) (gmap h b a Y (u j)) - h (u i : V) (u j : V) =
        (h (gmap h b a Y (u i)) (gmap h b a Y (u j)) - h (v i : V) (v j : V)) +
          (h (v i : V) (v j : V) - h (u i : V) (u j : V)) := by ring
    rw [e]
    refine add_mem (J.h_sub_mem _ _ _ _ (v i).2 (v j).2 (hgv i) (hgv j)) ?_
    rw [HU.mem_SP_iff_locF]
    exact hP (u i) (u j) (v i) (v j) (hv i) (hv j)
  · have hc : J.E Y hYA ∘ₗ J.Psi = P ∘ₗ J.Psi := by
      refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, LinearMap.coe_single, Psi_apply]
      rw [E_mk]
      change _ = P (Submodule.Quotient.mk (u j))
      rw [← hv j, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply,
        Submodule.coe_sub]
      exact hgv j
    refine LinearMap.ext fun q => ?_
    obtain ⟨w, rfl⟩ := J.Psi_surjective q
    exact LinearMap.congr_fun hc w

end JD

end Formalism.L2.SG.Pf.fibreCountingData
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingData

section

@[expose] public section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

def liftQ {K F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    (M : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) : Matrix (Fin m) (Fin m) (𝓞 K) :=
  Matrix.of fun i j => (Ideal.Quotient.mk_surjective (M i j)).choose

theorem liftQ_map {K F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    (M : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (liftQ M).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = M := by
  ext i j
  simp only [Matrix.map_apply, liftQ, Matrix.of_apply]
  exact (Ideal.Quotient.mk_surjective (M i j)).choose_spec

end Formalism.L2.SG.Pf.fibreCountingData

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G5 Formalism.L2.SG.Pf.discriminantNormShapes Formalism.L2.SG.Pf.fibreCountingData

theorem unitary_discriminant_model : UDModel := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ _ hK h hs hd L hL hLi 𝔭 h𝔭 b a hb k hk
  have hli := linearIndependent_of_jordan hb
  have hcard : Fintype.card (Fin (finrank K (⊤ : Submodule K V))) = finrank K V := by
    simp [finrank_top]
  have hbspan := hli.span_eq_top_of_card_eq_finrank' hcard
  obtain ⟨-, hloc, horth, hdiag, hne⟩ := hb
  have hfull : Submodule.span K (L : Set V) = ⊤ := by
    apply top_unique
    rw [← hbspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hmem : b i ∈ locF 𝔭 L := by
      rw [← hloc]
      exact Formalism.HermitianLattices.Ext.L3.localizedQuotients.le_locF 𝔭 _
        (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨s, hs, hsx⟩ := hmem
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      clear hsx
      induction hs using Submonoid.closure_induction with
      | mem y hy =>
        obtain ⟨t, ht, rfl⟩ := hy
        rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K,
          IsScalarTower.algebraMap_apply (𝓞 F) F K]
        exact (map_ne_zero (algebraMap F K)).2
          ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (fun ht0 => ht (ht0 ▸ 𝔭.zero_mem)))
      | one => simp
      | mul x y _ _ hx hy => simp only [map_mul]; exact mul_ne_zero hx hy
    have hsx' : algebraMap (𝓞 K) K s • b i ∈ Submodule.span K (L : Set V) := by
      rw [algebraMap_smul]; exact Submodule.subset_span hsx
    exact (Submodule.smul_mem_iff _ hs0).1 hsx'
  have hFx : IsFixF K F := Fact.out
  let s := udSetoid K 𝔭 k a
  let J : JD h L 𝔭 b a := ⟨horth, hdiag, hne, hloc, hFx, h𝔭, ⟨hL.fg, hfull⟩⟩
  have := h𝔭.isPrime
  have hv : ∀ i, vF 𝔭 (a i) ≤ vJof 𝔭 a := fun i =>
    Finset.single_le_sum (f := fun i => vF 𝔭 (a i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hk1 : ∀ i, vF 𝔭 (a i) ≤ k := fun i => by have := hv i; omega
  have hk2 : ∀ i j, vF 𝔭 (a i) + vF 𝔭 (a j) ≤ k := fun i j => by
    have := hv i; have := hv j; omega
  have hA : ∀ Y : udPre K 𝔭 k a, ∀ i j,
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i) * liftQ Y.1 i j) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ HU.SP K 𝔭 := fun Y =>
    (condP_iff_eqP hne hk1 (liftQ Y.1)).1 (by rw [liftQ_map]; exact Y.2.1)
  have hW : ∀ Y : udPre K 𝔭 k a, ∀ i j,
      algebraMap (𝓞 K) K (gramO a (liftQ Y.1) i j) / (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) * algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j))) ∈ HU.SP K 𝔭 := fun Y =>
    (condW_iff hne hk2 (liftQ Y.1)).1 (by rw [liftQ_map]; exact Y.2.2)
  let f0 : udPre K 𝔭 k a → {P : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) //
      ∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
        Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
        Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
        h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)} :=
    fun Y => ⟨J.E (liftQ Y.1) (hA Y), J.E_isom (liftQ Y.1) (hA Y) (hW Y)⟩
  have hresp : ∀ Y Y' : udPre K 𝔭 k a, s.r Y Y' → f0 Y = f0 Y' := by
    rintro Y Y' ⟨Z, hZ⟩
    have hd := (condZ_iff hne hk1 (liftQ Y.1) (liftQ Y'.1)).mp
      ⟨Z, by simpa only [liftQ_map] using hZ⟩
    exact Subtype.ext (J.E_eq_of (liftQ Y.1) (liftQ Y'.1) (hA Y) (hA Y') hd)
  let f : udQ K 𝔭 k a → _ := Quotient.lift (s := s) f0 hresp
  have hinj : Function.Injective f := by
    intro q q'
    induction q using Quotient.inductionOn with | h Y => ?_
    induction q' using Quotient.inductionOn with | h Y' => ?_
    intro he
    have he' : J.E (liftQ Y.1) (hA Y) = J.E (liftQ Y'.1) (hA Y') := congrArg Subtype.val he
    apply Quotient.sound
    obtain ⟨Z, hZ⟩ := (condZ_iff hne hk1 (liftQ Y.1) (liftQ Y'.1)).2
      (J.entry_of_E_eq (liftQ Y.1) (liftQ Y'.1) (hA Y) (hA Y') he')
    rw [liftQ_map, liftQ_map] at hZ
    exact ⟨Z, hZ⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨P, hP⟩
    have hLift := J.exists_E_eq P hP
    rcases hLift with ⟨Y, hY, hWY, hE⟩
    let Yq : udPre K 𝔭 k a :=
      ⟨Y.map (Ideal.Quotient.mk _), (condP_iff_eqP hne hk1 Y).2 hY, (condW_iff hne hk2 Y).2 hWY⟩
    refine ⟨Quotient.mk _ Yq, Subtype.ext ?_⟩
    refine (J.E_eq_of (liftQ Yq.1) Y (hA Yq) hY fun i j => ?_).trans hE
    have e := congrFun (congrFun (liftQ_map (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))) i) j
    rw [map_apply, map_apply, Ideal.Quotient.eq] at e
    exact div_mem_SP_of_mem h𝔭 (hne j) (hk1 j) e
  rw [discAut]
  exact (Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩).symm

end Formalism.L2.SG.Pf.Cnt
end
end
end
