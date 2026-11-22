export class CliUsageError extends Error {}

export function optionValue(argv: string[], index: number): string {
  const value = argv[index + 1];
  if (value === undefined || !value.trim() || value.startsWith("--")) {
    throw new CliUsageError(`${argv[index]} requires a value`);
  }
  return value;
}
