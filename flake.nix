{
  inputs = {
    flake-utils.url = github:numtide/flake-utils;
    git-ignore-nix.url = github:hercules-ci/gitignore.nix/master;
  };
  outputs = { self, flake-utils, nixpkgs, git-ignore-nix }:
  let
    hpath = { prefix ? null, compiler ? null }:
      (if prefix == null then [] else [ prefix ]) ++
      (if compiler == null
       then [ "haskellPackages" ]
       else [ "haskell" "packages" compiler ]
      );
    fromHOL = hol: comp: final: prev: with prev.lib; with attrsets;
      let setAttrByPath' = base: path: to: recursiveUpdate
            { ${head path} = base.${head path}; }
            (setAttrByPath path to);
      in  setAttrByPath' prev (hpath comp)
            ((getAttrFromPath (hpath comp) prev).override (old: {
              overrides = composeExtensions (old.overrides or (_: _: {}))
                (hol final prev);
            }));
    hoverlay = final: prev: hself: hsuper: {
      th-canonical = hself.callCabal2nix "th-canonical"
        (git-ignore-nix.lib.gitignoreSource ./.) { };
    };
    defComp = if builtins.pathExists ./comp.nix
      then import ./comp.nix
      else { };
    overlay = fromHOL hoverlay defComp;
    overlays = [ overlay ];
  in flake-utils.lib.eachDefaultSystem (system:
  let pkgs = import nixpkgs { inherit system overlays; };
      hpkg = pkgs.lib.attrsets.getAttrFromPath (hpath defComp) pkgs;
  in
  rec {
    devShell = hpkg.shellFor {
      packages = p: [ p.th-canonical ];
    };
    defaultPackage = hpkg.th-canonical;
  }) // { inherit hoverlay overlay overlays; };
}
