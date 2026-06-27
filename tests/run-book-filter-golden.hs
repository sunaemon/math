module Main where

import Control.Monad (forM_, unless, when)
import Data.Maybe (fromMaybe)
import System.Directory (
  createDirectoryIfMissing,
  doesDirectoryExist,
  doesFileExist,
  getCurrentDirectory,
  getTemporaryDirectory,
  removeDirectoryRecursive,
 )
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..), exitFailure)
import System.FilePath (takeFileName, (</>))
import System.IO (hPutStrLn, stderr)
import System.Process (
  CreateProcess (cwd),
  proc,
  readCreateProcessWithExitCode,
  readProcessWithExitCode,
 )

data Golden = Golden
  { goldenName :: String
  , goldenInput :: FilePath
  , goldenExpected :: FilePath
  }

data FailureCase = FailureCase
  { failureName :: String
  , failureInput :: FilePath
  , failureExpectedStderr :: String
  }

main :: IO ()
main = do
  root <- getCurrentDirectory
  let filterBin = root </> "build" </> "book-filter"
  filterExists <- doesFileExist filterBin
  unless filterExists $ do
    hPutStrLn stderr ("missing filter binary: " <> filterBin)
    hPutStrLn stderr "run `make build/book-filter` or `make test`"
    exitFailure

  tmpBase <- getTemporaryDirectory
  let tmp = tmpBase </> "book-filter-golden"
  removeIfExists tmp
  createDirectoryIfMissing True tmp

  goldenFailures <-
    mapM
      (runGolden root tmp filterBin)
      [ Golden
          "section references and notation links"
          ("tests" </> "fixtures" </> "section-notation.md")
          ("tests" </> "golden" </> "section-notation.tex")
      , Golden
          "mathmeta typed free-variable notation"
          ("tests" </> "fixtures" </> "mathmeta-freevars.md")
          ("tests" </> "golden" </> "mathmeta-freevars.tex")
      , Golden
          "mathmeta with scope preserves nested directives"
          ("tests" </> "fixtures" </> "mathmeta-with-nested.md")
          ("tests" </> "golden" </> "mathmeta-with-nested.tex")
      , Golden
          "mathmeta with scope applies inside nested block lists"
          ("tests" </> "fixtures" </> "mathmeta-with-nested-local-scope.md")
          ("tests" </> "golden" </> "mathmeta-with-nested-local-scope.tex")
      , Golden
          "half-open intervals after commands keep their brackets"
          ("tests" </> "fixtures" </> "math-bracket-intervals.md")
          ("tests" </> "golden" </> "math-bracket-intervals.tex")
      , Golden
          "a malformed term marker does not block later well-formed markers"
          ("tests" </> "fixtures" </> "term-marker-malformed-recovery.md")
          ("tests" </> "golden" </> "term-marker-malformed-recovery.tex")
      , Golden
          "a term argument ending in an escaped backslash parses correctly"
          ("tests" </> "fixtures" </> "term-arg-trailing-backslash.md")
          ("tests" </> "golden" </> "term-arg-trailing-backslash.tex")
      , Golden
          "raw hierarchical \\index subentries pass through; flat entries become term entries"
          ("tests" </> "fixtures" </> "raw-index-entries.md")
          ("tests" </> "golden" </> "raw-index-entries.tex")
      ]

  expectedFailures <-
    mapM
      (runExpectedFailure root filterBin)
      [ FailureCase
          "notation use before definition is rejected"
          ("tests" </> "fixtures" </> "bad-notation-before-define.md")
          "[notation-filter] notation used before \\define or \\forward:"
      , FailureCase
          "forwarded notation must later be defined"
          ("tests" </> "fixtures" </> "bad-forward-without-define.md")
          "[notation-filter] notation forwarded but never defined:"
      , FailureCase
          "forwarded terms must later be defined"
          ("tests" </> "fixtures" </> "bad-term-forward-without-define.md")
          "[term-filter] term forwarded but never defined:"
      , FailureCase
          "dangling section references are rejected"
          ("tests" </> "fixtures" </> "bad-section-ref.md")
          "[ref-filter] dangling section reference(s):"
      , FailureCase
          "scope end without scope begin is rejected"
          ("tests" </> "fixtures" </> "bad-decl-scope-end.md")
          "\\scopeend without matching \\scopebegin"
      , FailureCase
          "export end without export begin is rejected"
          ("tests" </> "fixtures" </> "bad-decl-export-end.md")
          "\\exportend without matching \\export{...}"
      , FailureCase
          "import of an unknown export is rejected"
          ("tests" </> "fixtures" </> "bad-decl-import.md")
          "\\import{missing} references an unknown export"
      , FailureCase
          "nested declaration exports are rejected"
          ("tests" </> "fixtures" </> "bad-decl-nested-export.md")
          "\\export{inner} started before closing active \\export{outer}"
      , FailureCase
          "unclosed declaration scope is rejected"
          ("tests" </> "fixtures" </> "bad-decl-unclosed-scope.md")
          "\\scopebegin without matching \\scopeend"
      , FailureCase
          "unclosed declaration export is rejected"
          ("tests" </> "fixtures" </> "bad-decl-unclosed-export.md")
          "\\export{dangling} without matching \\exportend"
      , FailureCase
          "mathmeta notationtype requires a declared type"
          ("tests" </> "fixtures" </> "bad-mathmeta-unknown-notation-type.md")
          "references an unknown type; add \\type{typo-type} before using it"
      , FailureCase
          "mathmeta with rejects notation directives"
          ("tests" </> "fixtures" </> "bad-mathmeta-with-define.md")
          "malformed mathmeta block"
      , FailureCase
          "mathmeta with inside nested block does not leak outward"
          ("tests" </> "fixtures" </> "bad-mathmeta-with-nested-leak.md")
          "could not infer the syntactic type of a typed notation argument"
      ]

  successFailures <-
    mapM
      (runExpectedSuccess root tmp filterBin)
      [
        ( "dependency graph tolerates a chapter outside any \\part"
        , "tests" </> "fixtures" </> "dependency-graph-partless-chapter.md"
        )
      ]

  lintFailures <- runLintTests tmp filterBin

  injectFailures <- runInjectBooklinksTests tmp filterBin

  let failures =
        concat goldenFailures
          ++ concat expectedFailures
          ++ concat successFailures
          ++ lintFailures
          ++ injectFailures
  unless (null failures) $ do
    hPutStrLn stderr ""
    hPutStrLn stderr "book-filter golden tests failed:"
    forM_ failures (hPutStrLn stderr . ("  " <>))
    exitFailure

removeIfExists :: FilePath -> IO ()
removeIfExists path = do
  exists <- doesFileExist path
  if exists
    then removeDirectoryRecursive path
    else do
      dirExists <- doesDirectoryExist path
      when dirExists $ removeDirectoryRecursive path

runGolden :: FilePath -> FilePath -> FilePath -> Golden -> IO [String]
runGolden root tmp filterBin test = do
  let input = root </> goldenInput test
      expected = root </> goldenExpected test
      actual = tmp </> takeFileName (goldenExpected test)
  (code, out, err) <- runPandoc filterBin input
  case code of
    ExitSuccess -> do
      writeFile actual out
      expectedText <- readFile expected
      if out == expectedText
        then pure []
        else do
          diff <- diffFiles expected actual
          pure [goldenName test <> " output differed\n" <> diff]
    ExitFailure n ->
      pure [goldenName test <> " exited with " <> show n <> "\n" <> err]

runExpectedFailure :: FilePath -> FilePath -> FailureCase -> IO [String]
runExpectedFailure root filterBin test = do
  let input = root </> failureInput test
  (code, _out, err) <- runPandoc filterBin input
  case code of
    ExitSuccess ->
      pure [failureName test <> " unexpectedly succeeded"]
    ExitFailure _ ->
      if failureExpectedStderr test `isInfixOf` err
        then pure []
        else pure [failureName test <> " failed with unexpected stderr\n" <> err]

-- A fixture that must filter without error, where the exact output is not
-- asserted (e.g. the dependency-graph layout, whose annealed positions and
-- cache hit/miss line are not portable to golden text). Runs with cwd set to
-- the temp dir so the relative `build/dependency-graph-layout.cache` the filter
-- writes lands there instead of clobbering the book's real layout cache.
runExpectedSuccess :: FilePath -> FilePath -> FilePath -> (String, FilePath) -> IO [String]
runExpectedSuccess root tmp filterBin (name, inputRel) = do
  let input = root </> inputRel
  pandocBin <- fromMaybe "pandoc" <$> lookupEnv "PANDOC_BIN"
  let process =
        (proc pandocBin [input, "-f", "markdown", "--filter", filterBin, "-t", "latex"])
          { cwd = Just tmp
          }
  (code, _out, err) <- readCreateProcessWithExitCode process ""
  case code of
    ExitSuccess -> pure []
    ExitFailure n ->
      pure [name <> " exited with " <> show n <> "\n" <> err]

runLintTests :: FilePath -> FilePath -> IO [String]
runLintTests tmp filterBin = do
  let okInput = tmp </> "lint-ok.md"
      badInput = tmp </> "lint-bad.md"
      fixInput = tmp </> "lint-fix.md"
      rawNotationInput = tmp </> "lint-raw-notation.md"
      rawNotationFixInput = tmp </> "lint-raw-notation-fix.md"
  writeFile okInput "short line\n"
  writeFile badInput "short line\nthis line is too long\n"
  writeFile fixInput "short line\nthis line is too long\n"
  writeFile rawNotationInput "Use $\\mathbb{N}$, $\\omega_1^{CK}$, $\\aleph_1$, $\\beth_\\alpha$, and $A \\subseteq B \\setminus C$ here.\n"
  writeFile rawNotationFixInput "Use $\\mathbb{N}$, $\\mathbb{R}$, $\\omega_1$, $\\omega_1^{CK}$, $\\aleph_0$, $\\aleph_1$, $\\beth_\\alpha$, and $A \\subsetneq B \\setminus (C \\setminus D) \\subseteq E$ here.\n"
  okFailures <- runLintSuccess filterBin okInput
  badFailures <- runLintExpectedFailure filterBin badInput
  fixFailures <- runLintFix filterBin fixInput
  rawNotationFailures <- runLintRawNotationExpectedFailure filterBin rawNotationInput
  rawNotationFixFailures <- runLintRawNotationFix filterBin rawNotationFixInput
  pure
    ( okFailures
        ++ badFailures
        ++ fixFailures
        ++ rawNotationFailures
        ++ rawNotationFixFailures
    )

runLintSuccess :: FilePath -> FilePath -> IO [String]
runLintSuccess filterBin input = do
  (code, _out, err) <-
    readProcessWithExitCode
      filterBin
      ["lint", "--max-line-length=30", input]
      ""
  case code of
    ExitSuccess -> pure []
    ExitFailure n ->
      pure ["line-length lint unexpectedly failed with " <> show n <> "\n" <> err]

runLintExpectedFailure :: FilePath -> FilePath -> IO [String]
runLintExpectedFailure filterBin input = do
  (code, _out, err) <-
    readProcessWithExitCode
      filterBin
      ["lint", "--max-line-length=12", "--max-reports=1", input]
      ""
  case code of
    ExitSuccess ->
      pure ["line-length lint unexpectedly succeeded"]
    ExitFailure _ ->
      if "[lint] source lint failed:" `isInfixOf` err
        && ":2: line length 21 > 12" `isInfixOf` err
        then pure []
        else pure ["line-length lint failed with unexpected stderr\n" <> err]

runLintFix :: FilePath -> FilePath -> IO [String]
runLintFix filterBin input = do
  (code, _out, err) <-
    readProcessWithExitCode
      filterBin
      ["lint", "--fix", "--max-line-length=12", input]
      ""
  fixed <- readFile input
  case code of
    ExitSuccess
      | fixed == "short line\nthis line is\ntoo long\n" ->
          pure []
      | otherwise ->
          pure ["line-length lint fix produced unexpected output\n" <> fixed]
    ExitFailure n ->
      pure ["line-length lint fix unexpectedly failed with " <> show n <> "\n" <> err]

runLintRawNotationExpectedFailure :: FilePath -> FilePath -> IO [String]
runLintRawNotationExpectedFailure filterBin input = do
  (code, _out, err) <-
    readProcessWithExitCode
      filterBin
      ["lint", "--macros=polish-space/tex/macros.tex", input]
      ""
  case code of
    ExitSuccess ->
      pure ["raw-notation lint unexpectedly succeeded"]
    ExitFailure _ ->
      if "prohibited raw notation \\mathbb{N}; use \\NN instead" `isInfixOf` err
        && "prohibited raw notation \\subseteq; use \\IncludedIn instead" `isInfixOf` err
        && "prohibited raw notation \\setminus; use \\SetDifference instead" `isInfixOf` err
        && "prohibited raw notation \\omega_1^{CK}; use \\churchKleeneOrd instead" `isInfixOf` err
        && "prohibited raw notation \\aleph_; use \\alephCard instead" `isInfixOf` err
        && "prohibited raw notation \\beth_; use \\bethCard instead" `isInfixOf` err
        then pure []
        else pure ["raw-notation lint failed with unexpected stderr\n" <> err]

runLintRawNotationFix :: FilePath -> FilePath -> IO [String]
runLintRawNotationFix filterBin input = do
  (code, _out, err) <-
    readProcessWithExitCode
      filterBin
      ["lint", "--fix", "--macros=polish-space/tex/macros.tex", input]
      ""
  fixed <- readFile input
  case code of
    ExitSuccess
      | fixed == "Use $\\NN$, $\\R$, $\\omegaOneOrd$, $\\churchKleeneOrd$, $\\alephNull$, $\\alephCard{1}$, $\\bethCard{\\alpha}$, and $A\n\\StrictlyIncludedIn \\SetDifference{B}{(\\SetDifference{C}{D})} \\IncludedIn E$ here.\n" ->
          pure []
      | otherwise ->
          pure ["raw-notation lint fix produced unexpected output\n" <> fixed]
    ExitFailure n ->
      pure ["raw-notation lint fix unexpectedly failed with " <> show n <> "\n" <> err]

-- The inject-booklinks subcommand consumes a sourcemap whose match.source must
-- equal the --source path, so the fixtures are generated in the temp dir (like
-- the lint tests) rather than checked in.
runInjectBooklinksTests :: FilePath -> FilePath -> IO [String]
runInjectBooklinksTests tmp filterBin = do
  happy <- happyPath
  inlineMath <-
    expectedError "inline-math" "Value $x$ here.\n" [(7, 13)] "falls inside inline math"
  overlap <-
    expectedError "overlap" "alpha beta gamma\n" [(0, 10), (6, 16)] "overlapping source-map spans"
  skip <- skipPath
  pure (happy ++ inlineMath ++ overlap ++ skip)
 where
  sourceFile = tmp </> "inject-source.md"
  mapFile = tmp </> "inject-map.json"
  outFile = tmp </> "inject-out.md"

  -- A "skips" array injects \SkipStart{key}/\SkipEnd{key} at the span ends,
  -- coexisting with booklink entries in the same map and pass.
  writeSkipMap :: IO ()
  writeSkipMap =
    writeFile mapFile $
      unlines
        [ "{"
        , "  \"entries\": [],"
        , "  \"skips\": ["
        , "    {"
        , "      \"source\": \"" ++ sourceFile ++ "\","
        , "      \"kind\": \"block\","
        , "      \"key\": \"chap-6\","
        , "      \"startLine\": 1,"
        , "      \"startOffset\": 6,"
        , "      \"endOffset\": 23"
        , "    }"
        , "  ]"
        , "}"
        ]

  skipPath = do
    writeFile sourceFile "Kept. Skipped sentence. Kept.\n"
    writeSkipMap
    (code, _out, err) <- runInject
    case code of
      ExitFailure n -> pure ["inject-booklinks skip path failed with " <> show n <> "\n" <> err]
      ExitSuccess -> do
        result <- readFile outFile
        let ok =
              "Kept. \\SkipStart{chap-6}Skipped sentence.\\SkipEnd{chap-6} Kept." `isInfixOf` result
        if ok
          then pure []
          else pure ["inject-booklinks skip path produced unexpected output\n" <> result]

  runInject =
    readProcessWithExitCode
      filterBin
      ["inject-booklinks", "--sourcemap", mapFile, "--source", sourceFile, "--out", outFile]
      ""

  -- A minimal, deliberately flat sourcemap: the parser is line-based and only
  -- looks for declName/target/match/status/source/startOffset/endOffset lines.
  writeSourceMap :: [(Int, Int)] -> IO ()
  writeSourceMap spans =
    writeFile mapFile $
      unlines (["{", "  \"entries\": ["] ++ concat (zipWith entry [0 ..] spans) ++ ["  ]", "}"])

  entry :: Int -> (Int, Int) -> [String]
  entry idx (start, end) =
    [ "    {"
    , "      \"declName\": \"decl" ++ show idx ++ "\","
    , "      \"target\": \"prose\","
    , "      \"match\": {"
    , "        \"status\": \"matched\","
    , "        \"source\": \"" ++ sourceFile ++ "\","
    , "        \"startOffset\": " ++ show start ++ ","
    , "        \"endOffset\": " ++ show end
    , "      }"
    , "    }"
    ]

  happyPath = do
    writeFile sourceFile "The space X is Polish.\n"
    writeSourceMap [(15, 21)]
    (code, _out, err) <- runInject
    case code of
      ExitFailure n -> pure ["inject-booklinks happy path failed with " <> show n <> "\n" <> err]
      ExitSuccess -> do
        result <- readFile outFile
        let ok =
              "\\BooklinkStart[entry=0]{" `isInfixOf` result
                && "}Polish" `isInfixOf` result
                && "Polish\\BooklinkEnd[entry=0]{" `isInfixOf` result
        if ok
          then pure []
          else pure ["inject-booklinks happy path produced unexpected output\n" <> result]

  expectedError name source spans needle = do
    writeFile sourceFile source
    writeSourceMap spans
    (code, _out, err) <- runInject
    case code of
      ExitSuccess -> pure ["inject-booklinks " <> name <> " unexpectedly succeeded"]
      ExitFailure _ ->
        if needle `isInfixOf` err
          then pure []
          else pure ["inject-booklinks " <> name <> " failed with unexpected stderr\n" <> err]

runPandoc :: FilePath -> FilePath -> IO (ExitCode, String, String)
runPandoc filterBin input = do
  pandocBin <- fromMaybe "pandoc" <$> lookupEnv "PANDOC_BIN"
  readProcessWithExitCode
    pandocBin
    [ input
    , "-f"
    , "markdown"
    , "--filter"
    , filterBin
    , "-t"
    , "latex"
    ]
    ""

diffFiles :: FilePath -> FilePath -> IO String
diffFiles expected actual = do
  (code, out, err) <- readProcessWithExitCode "diff" ["-u", expected, actual] ""
  pure $ case code of
    ExitSuccess -> ""
    ExitFailure _ -> out <> err

isInfixOf :: (Eq a) => [a] -> [a] -> Bool
isInfixOf needle haystack =
  any (needle `prefixOf`) (tails haystack)

prefixOf :: (Eq a) => [a] -> [a] -> Bool
prefixOf [] _ = True
prefixOf _ [] = False
prefixOf (x : xs) (y : ys) = x == y && prefixOf xs ys

tails :: [a] -> [[a]]
tails [] = [[]]
tails xs@(_ : rest) = xs : tails rest
