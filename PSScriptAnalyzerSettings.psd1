# PSScriptAnalyzer settings for the install and LLVM build scripts.
@{
    Severity = @('Error', 'Warning')
    ExcludeRules = @(
        # The scripts call their own Run helper positionally, like a shell
        # command; named parameters would only add noise.
        'PSAvoidUsingPositionalParameters'
        # Fires on the intentional `2>$null` stderr redirection.
        'PSPossibleIncorrectUsageOfRedirectionOperator'
    )
}
