module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RGHyp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.XLeSpanRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DetZhatSwapUnit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GramMMUnitOfTerm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalCountOfGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MkWEqOfSubMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExistsOfMemSmulLat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SmulCancelQ
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgBwdSup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianW0SpanZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgFwdSup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueConvPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueEtaPf
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgBwdSub

section

@[expose] public section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG6

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem rg_bwd_sub (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hG : (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
      GamR H t₂ (algebraMap F E (g.q : F))) :
    Prod.map φ' φ '' H.iotaGraph g t₁ ⊆ H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ := by
  rintro _ ⟨⟨y', y⟩, ⟨x₁', x₁, hx₁'L, hx₁L, hd₁, hpe⟩, rfl⟩
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  have hcO : algebraMap F E (g.q : F) ∈ M.L.O := by
    rw [M.L.O_def]
    have := isIntegral_algebraMap (R := ↥𝒪[F]) (A := E) (x := g.q)
    convert this using 1
    rw [IsScalarTower.algebraMap_apply (↥𝒪[F]) F E]
    rfl
  set c := algebraMap F E (g.q : F) with hc
  have hcx : ∀ x ∈ Λ₂, c • x ∈ Λ₂ := fun x hx => Λ₂.smul_mem (⟨c, hcO⟩ : M.L.O) hx
  obtain ⟨l, hl, hle⟩ := exists_of_mem_smulLat H hd₁
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₁ (x₁ : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₁ (x₁' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₁ l
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₁ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hle
  have hap : a ∈ H.perp (H.X t₁.f) := by
    have : a = (x₁ : V) - b := by rw [← hab]; abel
    rw [this]
    exact (H.perp _).sub_mem x₁.2 (mem_perp_isotropicSpan_of_mem_framePerp H hb)
  have hap' : a' ∈ H.perp (H.X t₁.f') := by
    have : a' = (x₁' : V) - b' := by rw [← hab']; abel
    rw [this]
    exact (H.perp _).sub_mem x₁'.2 (mem_perp_isotropicSpan_of_mem_framePerp' H hb')
  have haS : a ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha hb (by rw [hab]; exact hx₁L)
  have haS' : a' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha' hb' (by rw [hab']; exact hx₁'L)
  have haS'' : a'' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha'' hb'' (by rw [hab'']; exact hl)
  have hmemG : (θ (ddMk H t₁ ⟨a, haS⟩), θ (ddMk H t₁ ⟨a'', haS''⟩), φ (H.mkW t₁.f ⟨a, hap⟩),
      φ' (H.mkW t₁.f' ⟨a', hap'⟩)) ∈ GamR H t₂ c := by
    rw [← hG]
    exact ⟨_, ⟨⟨a, haS⟩, ⟨a', haS'⟩, ⟨a'', haS''⟩, hap, hap', hda, rfl⟩, rfl⟩
  obtain ⟨u, u', u'', hu, hu', huu, hpe2⟩ := hmemG
  simp only [Prod.mk.injEq] at hpe2
  obtain ⟨e1, e2, e3, e4⟩ := hpe2
  have key : ∀ (m : MMsharp H t₁) (n : MMsharp H t₂) (v : H.W0 t₁.f t₁.f'),
      θ (ddMk H t₁ m) = ddMk H t₂ n → (m : V) + v ∈ t₁.abelian₂ → (n : V) + ↑(ψ v) ∈ Λ₂ := by
    intro m n v hmn hv
    obtain ⟨w, hw1, hw2⟩ := (D.hθ m n).1 hmn
    have h1 : ((v - w : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
      have : ((v - w : H.W0 t₁.f t₁.f') : V) = ((m : V) + v) - ((m : V) + w) := by
        rw [Submodule.coe_sub]
        abel
      rw [this]
      exact t₁.abelian₂.sub_mem hv hw1
    have h2 := (D.hth (v - w)).1 h1
    have : (n : V) + ↑(ψ v) = ((n : V) + ↑(ψ w)) + ↑(ψ (v - w)) := by
      rw [map_sub, Submodule.coe_sub]
      abel
    rw [this]
    exact Λ₂.add_mem hw2 h2
  have hx₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ Λ₂ :=
    key ⟨a, haS⟩ u ⟨b, hb⟩ e1 (by
      show a + b ∈ _
      rw [hab]
      exact hx₁L)
  have hx₂'' : (u'' : V) + ↑(ψ ⟨b'', hb''⟩) ∈ Λ₂ :=
    key ⟨a'', haS''⟩ u'' ⟨b'', hb''⟩ e2 (by
      show a'' + b'' ∈ _
      rw [hab'']
      exact hl)
  have hbb : (⟨b', hb'⟩ : H.W0 t₁.f t₁.f') = ⟨b, hb⟩ - c • ⟨b'', hb''⟩ :=
    Subtype.ext (by
      show b' = b - c • b''
      rw [← hdb]
      abel)
  have hx₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ Λ₂ := by
    have e : (u' : V) + ↑(ψ ⟨b', hb'⟩) =
        ((u : V) + ↑(ψ ⟨b, hb⟩)) - c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩)) := by
      rw [hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Λ₂.sub_mem hx₂ (hcx _ hx₂'')
  have hp₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ H.perp (H.X t₂.f) :=
    (H.perp _).add_mem hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2)
  have hp₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ H.perp (H.X t₂.f') :=
    (H.perp _).add_mem hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2)
  have hd₂ : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) ∈ H.smulLat c Λ₂ := by
    have e : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) =
        c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩)) := by
      rw [hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Submodule.subset_span ⟨_, hx₂'', rfl⟩
  have hy : a + b ∈ H.perp (H.X t₁.f) := by
    rw [hab]
    exact x₁.2
  have hy' : a' + b' ∈ H.perp (H.X t₁.f') := by
    rw [hab']
    exact x₁'.2
  have hC : φ (H.mkW t₁.f ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H hb⟩) =
      H.mkW t₂.f ⟨↑(ψ ⟨b, hb⟩), mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2⟩ := D.hC1 ⟨b, hb⟩
  have hC' : φ' (H.mkW t₁.f' ⟨b', mem_perp_isotropicSpan_of_mem_framePerp' H hb'⟩) =
      H.mkW t₂.f' ⟨↑(ψ ⟨b', hb'⟩), mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2⟩ := D.hC1' ⟨b', hb'⟩
  have hφ : φ (H.mkW t₁.f x₁) = H.mkW t₂.f ⟨_, hp₂⟩ := by
    calc φ (H.mkW t₁.f x₁) = φ (H.mkW t₁.f ⟨a + b, hy⟩) :=
          congrArg φ (mkW_congr H x₁.2 hy hab.symm)
      _ = H.mkW t₂.f ⟨u, hu⟩ + H.mkW t₂.f ⟨↑(ψ ⟨b, hb⟩), mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2⟩ := by
          rw [mkW_add H a b hap (mem_perp_isotropicSpan_of_mem_framePerp H hb), map_add (f := _), e3, hC]
      _ = H.mkW t₂.f ⟨_, hp₂⟩ := (mkW_add H _ _ hu _).symm
  have hφ' : φ' (H.mkW t₁.f' x₁') = H.mkW t₂.f' ⟨_, hp₂'⟩ := by
    calc φ' (H.mkW t₁.f' x₁') = φ' (H.mkW t₁.f' ⟨a' + b', hy'⟩) :=
          congrArg φ' (mkW_congr H x₁'.2 hy' hab'.symm)
      _ = H.mkW t₂.f' ⟨u', hu'⟩ + H.mkW t₂.f' ⟨↑(ψ ⟨b', hb'⟩), mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2⟩ := by
          rw [mkW_add H a' b' hap' (mem_perp_isotropicSpan_of_mem_framePerp' H hb'), map_add (f := _), e4, hC']
      _ = H.mkW t₂.f' ⟨_, hp₂'⟩ := (mkW_add H _ _ hu' _).symm
  exact ⟨⟨_, hp₂'⟩, ⟨_, hp₂⟩, hx₂', hx₂, hd₂, Prod.ext hφ' hφ⟩

end RG6

end Formalism.L2.SG.LsDatumA
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgFwdSub

section

@[expose] public section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG4

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem rg_fwd_sub (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hI : Prod.map φ' φ '' H.iotaGraph g t₁ = H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩) :
    (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) ⊆
      GamR H t₂ (algebraMap F E (g.q : F)) := by
  set c : E := algebraMap F E (g.q : F) with hc
  have hcO : c ∈ M.L.O := q_mem_O g
  have hcL : ∀ (Λ : Submodule M.L.O V) {x : V}, x ∈ Λ → c • x ∈ Λ := by
    intro Λ x hx
    exact Λ.smul_mem (⟨c, hcO⟩ : M.L.O) hx
  have hMMU : ∀ (t : Term V M r) {x : V}, x ∈ MMsharp H t →
      x ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
    intro t x hx
    have h1 : x ∈ Submodule.span E (Set.range (H.MMfam t)) := hx.1
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨i, rfl⟩
    have hle : H.Xp t.f ⊔ H.Xp t.f' ≤ Submodule.span E (Set.range (Sum.elim t.f t.f')) :=
      sup_le
        (Submodule.span_mono (by
          rintro _ ⟨j, rfl⟩
          exact ⟨Sum.inl j, rfl⟩))
        (Submodule.span_mono (by
          rintro _ ⟨j, rfl⟩
          exact ⟨Sum.inr j, rfl⟩))
    exact hle (MMfam_mem_sup H t i)
  rintro _ ⟨p, ⟨u, u', u'', hu, hu', hd, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := D.hsurj₁ u
  obtain ⟨w'', hw''⟩ := D.hsurj₁ u''
  obtain ⟨w', hw'c⟩ : ∃ w' : ↥(H.W0 t₁.f t₁.f'), (w' : V) = (w : V) - c • (w'' : V) :=
    ⟨w - c • w'', rfl⟩
  have hw'eq : w' = w - c • w'' := Subtype.ext (by rw [hw'c]; rfl)
  have hψw' : (ψ w' : V) = (ψ w : V) - c • (ψ w'' : V) := by
    rw [hw'eq, map_sub, map_smul]
    rfl
  have hx : (u : V) + w ∈ H.perp (H.X t₁.f) := Submodule.add_mem _ hu (mem_perp_isotropicSpan_of_mem_framePerp H w.2)
  have hx' : (u' : V) + w' ∈ H.perp (H.X t₁.f') := Submodule.add_mem _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H w'.2)
  have hxL' : (u' : V) + w' ∈ t₁.abelian₂ := by
    have e : (u' : V) + w' = ((u : V) + w) - c • ((u'' : V) + w'') := by
      rw [hw'c, smul_add, ← hd]
      abel
    rw [e]
    exact Submodule.sub_mem _ hw (hcL _ hw'')
  have hdiffL : ((u : V) + w) - ((u' : V) + w') ∈ H.smulLat c t₁.abelian₂ := by
    have e : ((u : V) + w) - ((u' : V) + w') = c • ((u'' : V) + w'') := by
      rw [hw'c, smul_add, ← hd]
      abel
    rw [e]
    exact Submodule.subset_span ⟨_, hw'', rfl⟩
  have hmem : (φ' (H.mkW t₁.f' ⟨_, hx'⟩), φ (H.mkW t₁.f ⟨_, hx⟩)) ∈
      H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ := by
    rw [← hI]
    exact ⟨_, ⟨⟨_, hx'⟩, ⟨_, hx⟩, hxL', hw, hdiffL, rfl⟩, rfl⟩
  obtain ⟨y', y, hy'L, hyL, hyd, hyeq⟩ := hmem
  rw [Prod.mk.injEq] at hyeq
  obtain ⟨hyeq', hyeq2⟩ := hyeq
  obtain ⟨z, hzL, hz⟩ := exists_of_mem_smulLat H hyd
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₂ (y : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₂ (y' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₂ z
  have hx₂ : a + b ∈ H.perp (H.X t₂.f) := by
    rw [hab]
    exact y.2
  have hx₂' : a' + b' ∈ H.perp (H.X t₂.f') := by
    rw [hab']
    exact y'.2
  have hap : a ∈ H.perp (H.X t₂.f) := perp_left H (mem_perp_isotropicSpan_of_mem_framePerp H hb) hx₂
  have hap' : a' ∈ H.perp (H.X t₂.f') := perp_left H (mem_perp_isotropicSpan_of_mem_framePerp' H hb') hx₂'
  have h1 : φ (H.mkW t₁.f ⟨_, hx⟩) = H.mkW t₂.f ⟨a + b, hx₂⟩ :=
    hyeq2.trans (congrArg _ (Subtype.ext hab.symm))
  have h1' : φ' (H.mkW t₁.f' ⟨_, hx'⟩) = H.mkW t₂.f' ⟨a' + b', hx₂'⟩ :=
    hyeq'.trans (congrArg _ (Subtype.ext hab'.symm))
  obtain ⟨hbψ, hφ⟩ := RGHyp.trF H D (hMMU t₁ u.2) hu w hx ha hb hap hx₂ h1
  obtain ⟨hb'ψ, hφ'⟩ := RGHyp.trF' H D (hMMU t₁ u'.2) hu' w' hx' ha' hb' hap' hx₂' h1'
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₂ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hz
  have hb''ψ : b'' = ψ w'' := by
    apply smul_cancel_q g
    rw [← hdb, hbψ, hb'ψ, hψw']
    abel
  have haM : a ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha hb (by rw [hab]; exact hyL)
  have ha'M : a' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha' hb' (by rw [hab']; exact hy'L)
  have ha''M : a'' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha'' hb'' (by rw [hab'']; exact hzL)
  refine ⟨⟨a, haM⟩, ⟨a', ha'M⟩, ⟨a'', ha''M⟩, hap, hap', hda, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext hφ hφ'))
  · exact (D.hθ u ⟨a, haM⟩).mpr ⟨w, hw, by rw [← hbψ, hab]; exact hyL⟩
  · exact (D.hθ u'' ⟨a'', ha''M⟩).mpr ⟨w'', hw'', by rw [← hb''ψ, hab'']; exact hzL⟩

end RG4

end Formalism.L2.SG.LsDatumA
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobalCountOfModule

section

@[expose] public section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG8

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem rgHyp_of (M : Model F E) (hM : M.OK) {r n : ℕ} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    (hn : Module.finrank E V = n) (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂') (hyp : LocalCountHypotheses H t₁ f₂ f₂' φ φ')
    (Λ₂ : Submodule M.L.O V) (hg : H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩)
    (hth : ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ')
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩)
    (hθ : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂) :
    ∃ ψ, RGHyp H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ θ φ φ' := by
  have hT₁ := hyp.1.1
  have hT₂ := hg.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT₁.2.1.2.1, hT₁.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT₁.2.2.1.2.1, hT₁.2.2.1.2.2.1⟩
  have hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)) := hT₂.2.2.2.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT₁.2.2.2.1
  obtain ⟨ψ, -, hψc⟩ := corrIso_holds M r n V H hn t₁ f₂ f₂' φ φ' hyp hD₂
  have hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f') :=
    isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ (isUnit_Gdet H _ _ _ _ hT₁.2.2.2.2.1)
  have hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim f₂ f₂'))) (H.W0 f₂ f₂') :=
    isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hyp.2.1 hyp.2.2.1 hD₂ (isUnit_Gdet H _ _ _ _ hT₂.2.2.2.2.1)
  have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
  have hZ₁' : IsUnit (H.Zhat t₁.f' t₁.f).det := det_Zhat_swap_unit H _ _ hZ₁
  have hzφ : φ (H.mkW t₁.f ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩) =
      H.mkW f₂ ⟨f₂ (Fin.last r), z_mem_perpX H hyp.2.1⟩ := by
    have e := hyp.2.2.2.2.1 ⟨_, z_mem_perpX H hF₁⟩ ⟨_, z_mem_perpX H hyp.2.1⟩ rfl rfl
    simpa using e
  have hzφ' : φ' (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perpX H hF₁'⟩) =
      H.mkW f₂' ⟨f₂' (Fin.last r), z_mem_perpX H hyp.2.2.1⟩ := by
    have e := hyp.2.2.2.2.2 ⟨_, z_mem_perpX H hF₁'⟩ ⟨_, z_mem_perpX H hyp.2.2.1⟩ rfl rfl
    simpa using e
  obtain ⟨u, hu⟩ := hD₂
  have hoφ : φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
      ((↑u⁻¹ : E) * H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ := by
    have e : H.Dl f₂ f₂' (r + 1) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
        H.Dl t₁.f t₁.f' (r + 1) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.1 _ _ rfl rfl
    rw [← hu] at e
    calc φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)
        = (↑u⁻¹ : E) • ((u : E) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  obtain ⟨u', hu'⟩ : IsUnit (M.L.cj (H.Dl f₂ f₂' (r + 1))) := by rw [← hu]; exact (Units.isUnit u).map _
  have hoφ' : φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
      ((↑u'⁻¹ : E) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ := by
    have e : M.L.cj (H.Dl f₂ f₂' (r + 1)) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
        M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.2.1 _ _ (om'_swap H _ _) (om'_swap H _ _)
    rw [← hu'] at e
    calc φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)
        = (↑u'⁻¹ : E) • ((u' : E) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  have hC2'' := cond_second_of_iso H t₁.f' t₁.f f₂' f₂ t₁.T' t₁.T' hF₁' hyp.2.2.1 hZ₁' φ' _ hzφ' hoφ'
  refine ⟨ψ, {
    hU₂ := hU₂
    hU₁ := hU₁
    hsd₁ := hT₁.1
    hsd₂ := hT₂.1
    hMM₁ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyp.1.2.1 i)
    hMM₂ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hg.2.1 i)
    hth := fun w => hth w (ψ w) ((hψc _ _).2 ⟨w.2, rfl⟩)
    hθ := ?_
    hsurj₁ := surj_MMsharp M hM H t₁ hyp.1 hU₁
    hC1 := fun w => by
      obtain ⟨_, _, c₁, _⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
      exact c₁
    hC1' := fun w => by
      obtain ⟨_, _, _, c₂⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
      exact c₂
    hC2 := cond_second_of_iso H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T hF₁ hyp.2.1 hZ₁ φ _ hzφ hoφ
    hC2' := fun v hv hvp => by
      rw [← U_swap] at hv
      obtain ⟨v', hv', hv'p, e⟩ := hC2'' v hv hvp
      rw [U_swap] at hv'
      exact ⟨v', hv', hv'p, e⟩ }⟩
  intro m₁ m₂
  rw [hθ m₁ m₂]
  constructor
  · rintro ⟨n₁, n₂, hc, h1, h2⟩
    obtain ⟨hn₁, hψn⟩ := (hψc _ _).1 hc
    exact ⟨⟨n₁, hn₁⟩, h1, by rw [hψn]; exact h2⟩
  · rintro ⟨w, h1, h2⟩
    exact ⟨w, ψ w, (hψc _ _).2 ⟨w.2, rfl⟩, h1, h2⟩

theorem claimRG_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimRG M r n := by
  intro hsome V _ _ H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  obtain ⟨g, hs⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨ψ, D⟩ := rgHyp_of M hM H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  have core1 := fun hI => Set.Subset.antisymm (rg_fwd_sub H g D hI) (rg_fwd_sup H g D hI)
  have core2 := fun hG => Set.Subset.antisymm (rg_bwd_sub H g D hG) (rg_bwd_sup H g D hG)
  have hL1 := Lset_eq_snd H hM g hs t₁ hyp.1 D.hU₁
  have hL1' := Lset_eq_fst H hM g hs t₁ hyp.1 D.hU₁
  have hL2 := Lset_eq_snd H hM g hs (⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) hg D.hU₂
  have hL2' := Lset_eq_fst H hM g hs (⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) hg D.hU₂
  constructor
  · intro hR
    refine ⟨fun h => absurd (hs.symm.trans h) (by simp), fun g' hg' => ?_⟩
    rw [Option.some.inj (hg'.symm.trans hs)]
    exact core1 (hR.2.2.2.2 g hs)
  · rintro ⟨-, hGR⟩
    have hI := core2 (hGR g hs)
    have e : φ '' (Prod.snd '' H.iotaGraph g t₁) = Prod.snd '' (Prod.map φ' φ '' H.iotaGraph g t₁) := by
      rw [Set.image_image, Set.image_image]
      rfl
    have e' : φ' '' (Prod.fst '' H.iotaGraph g t₁) = Prod.fst '' (Prod.map φ' φ '' H.iotaGraph g t₁) := by
      rw [Set.image_image, Set.image_image]
      rfl
    refine ⟨(congrArg (φ '' ·) hL1).trans (e.trans ((congrArg (Prod.snd '' ·) hI).trans hL2.symm)),
      hyp.2.2.2.2.1,
      (congrArg (φ' '' ·) hL1').trans (e'.trans ((congrArg (Prod.fst '' ·) hI).trans hL2'.symm)),
      hyp.2.2.2.2.2, fun g' hg' => ?_⟩
    rw [Option.some.inj (hg'.symm.trans hs)]
    exact hI

theorem claimR_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimR M r n :=
  claimR_of_modes M r n (claimRL_at M r n hM) (claimRG_at M r n hM)

theorem localCount_of_module (M : Model F E) (r n : ℕ) (hM : M.OK) (h0 : ModSide0 M r n M.split.isSome)
    (hU : ModSideU M r n M.split.isSome) : Formalism.MainNotions.ThinScalesBound.FamilyLocalModel M r n :=
  localCount_of_glue M r n hM (PI.LocCntLat.GE.glueEta_holds M r) (PI.LocCntLat.GC.glueConv_holds M r)
    (genOfPrim_holds M r n) (claimR_at M r n hM) h0 hU

theorem globalCount_of_module (D : Formalism.BasicNotions.D7)
    (h0 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ModSide0 M D.R.rS D.R.r M.split.isSome))
    (hU : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ModSideU M D.R.rS D.R.r M.split.isSome)) : Formalism.MainNotions.ThinScalesBound.T2 D := by
  intro F _ _ _ E _ _ _ _ M hM
  exact localCount_of_module M D.R.rS D.R.r hM (h0 F E M hM) (hU F E M hM)

end RG8

end Formalism.L2.SG.LsDatumA
end
end
end
