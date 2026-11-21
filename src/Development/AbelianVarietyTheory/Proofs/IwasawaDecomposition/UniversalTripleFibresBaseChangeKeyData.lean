module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataBaseChangeKeyPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem tied_keyPB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Nontrivial S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (y : FrPt Xo c S) (z : FrPt Xo c S') (Φ : FibKey Xo S y.x) (Φ' : FibKey Xo S' z.x), FrMap φ y z → Tied e y.s y.u Φ → Tied e z.s z.u Φ' → KeyPB Φ'.key Φ.key φ.toRingHom := by
  open GlobalTheory GlobalTheory.CM GlobalTheory.Frames MonoidalCategory CartesianMonoidalCategory MonObj IsDedekindDomain MeasureTheory in
  intro E _ _ _ H Dw l Xo c g e S S' _ _ _ _ _ φ y z Φ Φ' hm ⟨ht, hg1, hv1⟩ ⟨ht', hg2, hv2⟩
  obtain ⟨hx, hu, hs⟩ := ((GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S' φ y).2.2 z).1 hm
  have fibKey_keyPB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] [Nontrivial S'] (φ : S →+* S') (x : Sp S ⟶ Xo.X) (x' : Sp S' ⟶ Xo.X) (Φ : FibKey Xo S x) (Φ' : FibKey Xo S' x') (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), x' = spMap φ ≫ x → SecTie Φ.m Φ.th s → SecTie Φ'.m Φ'.th s' → SecBC φ 1 x x' s s' → ∃ (hg : Φ'.T.g = Φ.T.g) (v' : Fin Φ'.T.g → (epsR S' ⟶ Φ'.T.t.G)) (hv' : IsLieBasis v'), KeyPB ({ Φ' with v := v', basis := hv' } : FibKey Xo S' x').key Φ.key φ ∧ ∀ i, (v' i).left ≫ Φ'.m.φ = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (Φ.v (i.cast hg)).left ≫ Φ.m.φ := by
    intro E _ _ _ H Dw l Xo S S' _ _ hS φ x x' Φ Φ' s s' hx ht ht' hs
    obtain ⟨n, hn⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ x x' (spMap φ) Φ.m Φ'.m hx).1
    obtain ⟨hg, -, w, hw⟩ := (pat_pullback E H S S' φ Φ.T).2 Φ'.T n hS
    obtain ⟨θ, hθ⟩ := GlobalTheory.ArcQBC.exists_pullSec n.φ Φ.th
    have hm : IsoMaps w Φ'.th θ := ((TieCalc.secTie_calc E H Dw l Xo S x Φ.T.t Φ.m Φ.th s ht).2 S' φ x' Φ'.T.t Φ'.m n s' w θ
      Φ'.th hx hn.symm hs hw hθ).1 ht'
    obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange S S' φ Φ.T.t.G Φ'.T.t.G n.φ n.cart Φ.T.t.semi.smooth Φ.T.g Φ.v Φ.basis
    have hb : ∀ (k : ℕ) (hk : k = Φ.T.g), IsLieBasis fun i : Fin k => u (i.cast hk) := by
      rintro _ rfl
      exact hu
    have hv : ∀ i : Fin Φ'.T.g, (u (i.cast hg)).left ≫ n.φ = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (Φ.v (i.cast hg)).left :=
      fun i => huv _
    have he : eSec Φ'.T.t.G ≫ n.φ = spMap φ ≫ eSec Φ.T.t.G := n.cm.e_comm.trans (congrArg (· ≫ eSec Φ.T.t.G) n.base)
    have hr : ∀ (e : Sp S' ⟶ Sp S) (_ : n.cm.e = e) (he : eSec Φ'.T.t.G ≫ n.φ = e ≫ eSec Φ.T.t.G),
        rigPullOf n.φ e he Φ.T.t.PP.L Φ.T.t.PP.rig = n.cm.rigPull Φ.T.t.PP.L Φ.T.t.PP.rig := by
      rintro _ rfl _
      rfl
    refine ⟨hg, fun i => u (i.cast hg), hb _ hg, ⟨n.φ, he, w, hg, GlobalTheory.CompanionTheory.Ar.dualMap φ, n.cart, hw.1, ?_, fun j i h => ?_,
      fun a => ?_, ?_, hv⟩, fun i => ?_⟩
    · exact (hr _ n.base he).symm ▸ hw.2
    · refine Eq.trans ?_ (hm j i)
      have le : (Φ.T.t.PP.L.pull n.φ).U j ≤ n.φ ⁻¹ᵁ Φ.T.t.PP.L.U (j PUnit.unit) := fun y hy => mem_pull.1 hy
      rw [hθ j le, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    · ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    · ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]
    · rw [← hn, ← Category.assoc, hv, Category.assoc]
  
  obtain ⟨hg, v', hv', hk, hv⟩ := fibKey_keyPB E H Dw l Xo S S' φ.toRingHom y.x z.x Φ Φ' y.s z.s hx ht ht' hs
  have hvv : v' = Φ'.v := by
    funext i
    apply Over.OverMorphism.ext
    apply Φ'.m.cart.1.hom_ext
    · rw [hv i, hv1, hv2, hu]
      rfl
    · rw [Over.w, Over.w]
  subst hvv
  exact hk

end GlobalTheory.KeyFourth
