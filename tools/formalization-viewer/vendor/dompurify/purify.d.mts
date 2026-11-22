declare const DOMPurify: {
  isSupported: boolean;
  sanitize(source: string, config?: Record<string, unknown>): string;
};
export default DOMPurify;
