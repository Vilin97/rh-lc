module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.HasFiniteLengthJacSub
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.BoundB
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Compact
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.ComplementaryOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.ConjProd
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.CuspPairIrr
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.PiTensorTwist
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.PosMkIff
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.RhoNuRhoOfC
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SomeRed
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import GroundTheory.LocalFields.PadicLogSeries
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNegStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverseStatement
import Mathlib.Tactic.Linter.HaveILetI
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm

-- Source module: CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.ConjDual

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace CompanionTheory.RgGu.NR

namespace ConjDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irrAdm' : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π hs hi =>
  (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi

theorem conj_chi (n : ℕ) (s : ℝ) (g : GL (Fin n) k) :
    starRingEnd ℂ ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) =
      ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) := by
  have h : ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s : ℂ) := rfl
  rw [h, ← Complex.ofReal_cpow (by unfold nabs; positivity), Complex.conj_ofReal]

end ConjDual

open ConjDual in
theorem conjDual (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ConjDual k := by
  intro n V _ _ ρ hs hi hu s
  obtain ⟨B, hsym, hpos, hinv⟩ := hu

  have key : ∀ (g : GL (Fin n) k) (x v : V), B (ρ g⁻¹ x) v = B x (ρ g v) := by
    intro g x v
    have := hinv g (ρ g⁻¹ x) v
    rw [← this, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

  have hsm : ∀ v : V, (B.flip v : Module.Dual ℂ V) ∈ smoothPart ρ.dual := by
    intro v
    let H₁ : Subgroup (GL (Fin n) k) :=
      { carrier := {g | ρ g v = v}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    let H₂ : Subgroup (GL (Fin n) k) :=
      { carrier := {g | ρ.dual g (B.flip v) = B.flip v}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by
          show ρ.dual 1 (B.flip v) = B.flip v
          rw [map_one, Module.End.one_apply]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hle : H₁ ≤ H₂ := by
      intro g hg
      show ρ.dual g (B.flip v) = B.flip v
      ext x
      have hg' : ρ g v = v := hg
      rw [Representation.dual_apply]
      show B (ρ g⁻¹ x) v = B x v
      rw [key, hg']
    exact Subgroup.isOpen_mono hle (hs v)
  let φ : V →ₗ⋆[ℂ] smoothPart ρ.dual := LinearMap.codRestrict (smoothPart ρ.dual) B.flip hsm
  have hφ : ∀ v x, ((φ v : smoothPart ρ.dual) : Module.Dual ℂ V) x = B x v := fun _ _ => rfl
  have heq : ∀ g v, φ (ρ g v) = contra ρ g (φ v) := by
    intro g v
    apply Subtype.ext
    ext x
    rw [hφ, contra_apply, hφ, key]
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    have h1 := hpos v hne
    have h2 : B v v = 0 := by
      have := congrArg (fun l : smoothPart ρ.dual => (l : Module.Dual ℂ V) v) hv
      simpa [hφ] using this
    rw [h2] at h1
    simp at h1
  have hsurj : Function.Surjective φ := by
    have hci : (contra ρ).IsIrreducible := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra irrAdm' ρ hs hi
    let U : Subrepresentation (contra ρ) :=
      { toSubmodule := LinearMap.range φ
        apply_mem_toSubmodule := by
          rintro g _ ⟨v, rfl⟩
          exact ⟨ρ g v, heq g v⟩ }
    have : Nontrivial V := by
      by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      obtain ⟨a, b, hab⟩ := hi.exists_pair_ne
      apply hab
      apply Subrepresentation.ext
      have : ∀ S : Subrepresentation ρ, S.toSubmodule = ⊤ := fun S => by
        ext x; simp [Subsingleton.elim x 0]
      rw [this a, this b]
    rcases hci.eq_bot_or_eq_top U with hU | hU
    · exfalso
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have : φ v ∈ U.toSubmodule := ⟨v, rfl⟩
      rw [hU] at this
      have h0 : φ v = 0 := (Submodule.mem_bot ℂ).1 this
      exact hv (hinj (by rw [h0, map_zero]))
    · intro l
      have : l ∈ U.toSubmodule := by rw [hU]; exact Submodule.mem_top
      exact this
  refine ⟨φ, ⟨hinj, hsurj⟩, fun g v => ?_⟩
  show φ (((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) • ρ g v) =
    ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) • contra ρ g (φ v)
  rw [LinearMap.map_smulₛₗ, conj_chi, heq]

end CompanionTheory.RgGu.NR

end
end
end

-- Source module: CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.ThetaContra

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil Zc Zc.Cos

namespace CompanionTheory.RgGu.NR

namespace HermB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontriv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  exact hne (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem congrProd {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : x = y) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) :
    Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

def yy (x : IrrGL (k := k)) (s : ℝ) : Fin 2 → IrrGL (k := k) := ![x.nu (-(s : ℂ)), x.nu (s : ℂ)]

theorem eqv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (g : G) (v : V) :
    e (ρ g v) = σ g (e v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v

theorem theta_contra (hGK : GKLocal k) {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin N) k) W) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  have E := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK (π.comp (thetaW k N))
    (by rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π]; exact hs) (by rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π]; exact hi)
  rwa [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π] at E

theorem hasSesq_of {G V V₁ V₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] (π : Representation ℂ G V)
    (π₁ : Representation ℂ G V₁) (π₂ : Representation ℂ G V₂) (hi : π.IsIrreducible) (e₁ : π.Equiv π₁)
    (hc : ConjEquiv π₁ π₂) (e₂ : π₂.Equiv (contra π)) : HasSesq π := by
  obtain ⟨φ0, hφb, hφi⟩ := hc
  let Φ : V →ₛₗ[starRingEnd ℂ] smoothPart π.dual :=
    (e₂.toLinearEquiv.toLinearMap.comp φ0).comp e₁.toLinearEquiv.toLinearMap
  have hΦ : ∀ v, Φ v = e₂ (φ0 (e₁ v)) := fun _ => rfl
  have hΦb : Function.Injective Φ := (e₂.toLinearEquiv.injective.comp hφb.1).comp e₁.toLinearEquiv.injective
  have hΦi : ∀ g v, Φ (π g v) = contra π g (Φ v) := fun g v => by rw [hΦ, hΦ, eqv e₁, hφi, eqv e₂]
  haveI := nontriv _ hi
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => (Φ w : Module.Dual ℂ V) v)
    (fun v v' w => map_add _ v v') (fun c v w => map_smul _ c v)
    (fun v w w' => by rw [map_add (f := _)]; rfl) (fun c v w => by rw [map_smulₛₗ]; rfl), ?_, ?_⟩
  · intro hB
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    refine hw (hΦb ((Subtype.ext (LinearMap.ext fun v => ?_)).trans (map_zero Φ).symm))
    exact LinearMap.congr_fun₂ hB v w
  · intro g v w
    show (Φ (π g w) : Module.Dual ℂ V) (π g v) = (Φ w : Module.Dual ℂ V) v
    rw [hΦi, contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end HermB


open HermB in
theorem herm_ofB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : ConjProd k) (h2 : ConjDual k) : Herm k := by
  intro x hxu s N hd hirr
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hGK : GKLocal k := GlobalTheory.T.local_langlands_of_irreducible_admissible hA
  change HasSesq (prodIrr (yy x s) hd)
  change (prodIrr (yy x s) hd).IsIrreducible at hirr

  obtain ⟨E5⟩ := theta_contra hGK (prodIrr (yy x s) hd) (isSmooth_prodIrr _ _) hirr
  obtain ⟨hd', ⟨E4⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse (k := k) (h := 2) (N := N) hA hGK (yy x s) hd

  let c : Fin 2 → ℝ := ![-s, s]
  have hM : ∑ _a : Fin 2, x.1 = N := by
    rw [← hd, Fin.sum_univ_two, Fin.sum_univ_two]; rfl
  let χ : Fin 2 → kˣ →* ℂˣ := fun a => absPow k ((c a : ℝ) : ℂ)
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => isSmoothChar_absPow _
  let πs : Fin 2 → Representation ℂ (GL (Fin x.1) k) x.2.rep.V := fun a => twist x.rep (detChar (Fin x.1) (χ a))
  let σs : Fin 2 → Representation ℂ (GL (Fin x.1) k) (smoothPart x.rep.dual) :=
    fun a => twist (contra x.rep) (detChar (Fin x.1) (χ a))
  have hsπ : ∀ a, IsSmooth (πs a) := fun a => isSmooth_twist x.2.rep.smooth (hχ a).detChar
  have hiπ : ∀ a, (πs a).IsIrreducible := fun a => isIrreducible_twist x.2.rep.irr _
  have hic : (contra x.rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr
  have hsσ : ∀ a, IsSmooth (σs a) := fun a => isSmooth_twist (isSmooth_contra _) (hχ a).detChar
  have hiσ : ∀ a, (σs a).IsIrreducible := fun a => isIrreducible_twist hic _
  have hcj := h1 2 N (fun _ => x.1) hM (fun _ => x.2.rep.V) (fun _ => smoothPart x.rep.dual) πs σs
    (fun a => h2 x.1 x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr hxu (c a))
  have E1 := prodIrrEquiv hM πs hsπ hiπ
  have E2 := prodIrrEquiv hM σs hsσ hiσ
  have e0 : ((-s : ℝ) : ℂ) = -(s : ℂ) := by push_cast; ring
  have keyπ : ∀ (t : kˣ →* ℂˣ) (ht : IsSmoothChar t),
      IrrGL.of (twist x.rep (detChar (Fin x.1) t)) (isSmooth_twist x.2.rep.smooth ht.detChar)
        (isIrreducible_twist x.2.rep.irr _) = x.tw t ht := by
    intro t ht
    have := IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr t ht
    rw [IrrGL.of_rep] at this
    exact this.symm
  have keyσ : ∀ (t : kˣ →* ℂˣ) (ht : IsSmoothChar t),
      IrrGL.of (twist (contra x.rep) (detChar (Fin x.1) t)) (isSmooth_twist (isSmooth_contra _) ht.detChar)
        (isIrreducible_twist hic _) = (dualCl x).tw t ht := by
    intro t ht
    have := IrrGL.tw_of (contra x.rep) (isSmooth_contra _) hic t ht
    rw [← GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA x] at this
    exact this.symm
  have fπ : (fun a => IrrGL.of (πs a) (hsπ a) (hiπ a)) = yy x s := by
    funext a
    rw [keyπ _ (hχ a)]
    fin_cases a
    · show x.tw (absPow k ((-s : ℝ) : ℂ)) _ = x.nu (-(s : ℂ))
      simp only [IrrGL.nu, e0]
    · rfl
  have fσ : (fun a => IrrGL.of (σs a) (hsσ a) (hiσ a)) = fun a => dualCl (yy x s (Fin.rev a)) := by
    funext a
    rw [keyσ _ (hχ a)]
    fin_cases a
    · show (dualCl x).tw (absPow k ((-s : ℝ) : ℂ)) _ = dualCl (x.nu (s : ℂ))
      rw [GlobalTheory.T.dual_class_twist_neg hA x (s : ℂ)]
      simp only [IrrGL.nu, e0]
    · show (dualCl x).tw (absPow k ((s : ℝ) : ℂ)) _ = dualCl (x.nu (-(s : ℂ)))
      rw [GlobalTheory.T.dual_class_twist_neg hA x (-(s : ℂ)), neg_neg]
      rfl
  obtain ⟨E0⟩ := congrProd fπ.symm hd hM
  obtain ⟨E3⟩ := congrProd fσ hM hd'
  exact hasSesq_of _ _ _ hirr (E0.trans E1.symm) hcj ((E2.trans E3).trans (E4.symm.trans E5))

end CompanionTheory.RgGu.NR

end
end
end

-- Source module: CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.RhoNuRhoReducibleC

section

@[expose] public section

namespace CompanionTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem redClC : RedCl k :=
  redCl_ofC k (someRed_of k (complementary_of signature) (compact k) (boundB k) (herm_ofB k (conjProd k) (conjDual k))
    (prodModel k)) (cuspUnit k) (cuspPairIrr k)

theorem rhoNuRhoReducibleC : CompanionTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := rhoNuRho_ofC fun k _ _ _ _ => redClC k

end CompanionTheory.RgGu.NR
end
end
